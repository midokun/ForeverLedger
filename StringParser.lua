local addonName, FL = ...

-- ============================================================================
-- ForeverLedger :: StringParser.lua — FL.Parser
--
-- TSM-compatible price-formula language:
--   * Tokenizer (Lua patterns): numbers, money literals (1g2s3c), percentages
--     (150%), identifiers, operators, parentheses, commas, item:ID and pasted
--     item links.
--   * Precedence-climbing parser producing a small AST:
--       {k="num",v}  {k="src",name,item}  {k="bin",op,l,r}  {k="neg",e}  {k="call",name,args}
--   * Recursive evaluator with a per-frame memo (FL.FrameTick), a depth guard
--     and a recursion guard for self-referencing sources (postmin/postmax/crafting).
--   * Base price sources backed by FL.Market / FL.DB.vendor / FL.GetItemSellPrice.
--
-- Nil semantics: an unavailable source yields nil; nil propagates through
-- arithmetic (so "dbmarket * 1.25" is nil without market data); min/max/avg
-- skip nil arguments and sources that are 0; first() skips nil and 0; the
-- comparison functions (check/ifgt/...) treat a nil comparison operand as 0.
-- A formula whose result is nil means "no price" for the caller.
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Cached globals
-- ----------------------------------------------------------------------------
local type, tonumber, tostring, pairs, select, pcall, error = type, tonumber, tostring, pairs, select, pcall, error
local strfind, strsub, strlower, strformat, strmatch = string.find, string.sub, string.lower, string.format, string.match
local floor, ceil, mabs, msqrt, huge = math.floor, math.ceil, math.abs, math.sqrt, math.huge
local tconcat = table.concat
local GetTime = GetTime or function() return 0 end
local wipe = wipe or table.wipe or function(t) for k in pairs(t) do t[k] = nil end return t end

-- ----------------------------------------------------------------------------
-- Constants
-- ----------------------------------------------------------------------------
local MAX_DEPTH = 64            -- maximum AST nesting (enforced by parser and evaluator)
local MAX_NESTED_EVAL = 16      -- maximum nested Evaluate calls (postmin -> minFormula -> ...)
local CACHE_LIMIT = 512         -- parsed / compiled formula strings kept before a cache reset
local MEMO_SWEEP_AT = 4096      -- new memo keys inserted before stale entries are swept
local MAX_ROUND_DIGITS = 20     -- clamp for round/roundup/rounddown digit arguments

local OPS = { ["+"] = true, ["-"] = true, ["*"] = true, ["/"] = true, ["^"] = true }
local UNIT_MULT = { g = 10000, s = 100, c = 1 }
local UNIT_RANK = { g = 3, s = 2, c = 1 }

local FUNC_ARITY = {
	min = { 1, nil }, max = { 1, nil }, avg = { 1, nil }, first = { 1, nil },
	check = { 2, 3 },
	ifgt = { 3, 4 }, ifgte = { 3, 4 }, iflt = { 3, 4 }, iflte = { 3, 4 }, ifeq = { 3, 4 },
	round = { 1, 2 }, roundup = { 1, 2 }, rounddown = { 1, 2 },
	abs = { 1, 1 }, sqrt = { 1, 1 },
}
local FUNC_USAGE = {
	min = "min(a, b, ...)", max = "max(a, b, ...)", avg = "avg(a, b, ...)", first = "first(a, b, ...)",
	check = "check(cond, ifPositive, otherwise)",
	ifgt = "ifgt(a, b, ifTrue, ifFalse)", ifgte = "ifgte(a, b, ifTrue, ifFalse)",
	iflt = "iflt(a, b, ifTrue, ifFalse)", iflte = "iflte(a, b, ifTrue, ifFalse)", ifeq = "ifeq(a, b, ifTrue, ifFalse)",
	round = "round(x [, digits])", roundup = "roundup(x [, digits])", rounddown = "rounddown(x [, digits])",
	abs = "abs(x)", sqrt = "sqrt(x)",
}
local FUNC_LIST = "min, max, avg, first, check, ifgt, ifgte, iflt, iflte, ifeq, round, roundup, rounddown, abs, sqrt"

-- Every price source the language accepts at parse time. The sources that
-- AdvancedFeatures registers later (crafting, avgbuy, avgsell, inventory) are
-- listed so formulas mentioning them parse before that file has loaded; until
-- they are registered they evaluate to nil.
local KNOWN_SOURCE_ORDER = {
	"dbmarket", "dbminbuyout", "dbhistorical", "dbregionmarket", "numauctions", "dbsalerate",
	"crafting", "vendorsell", "vendorbuy", "matprice", "avgbuy", "avgsell", "inventory",
	"undercut", "postmin", "postmax", "restocktarget",
}
local KNOWN_SOURCES = {}
for i = 1, #KNOWN_SOURCE_ORDER do
	KNOWN_SOURCES[KNOWN_SOURCE_ORDER[i]] = true
end

-- Sources whose value of 0 is real information (counts / settings) rather than
-- "no data". Every other source is a price, and a price <= 0 means unavailable.
local ZERO_IS_VALUE = { undercut = true, numauctions = true, dbsalerate = true, inventory = true, restocktarget = true }

-- ----------------------------------------------------------------------------
-- Namespace and state
-- ----------------------------------------------------------------------------
local Parser = FL.Parser or {}
FL.Parser = Parser
Parser.astCache = Parser.astCache or {}   -- formula string -> AST
Parser.memo = Parser.memo or {}           -- per-frame memo: key -> { tick=, time=, value= }
Parser.sources = Parser.sources or {}     -- source name -> fn(itemID, suffix)

local astCache, memo, sources = Parser.astCache, Parser.memo, Parser.sources
local compileCache = {}      -- formula string -> compiled { ast=, id=, src= }
local compileErrors = {}     -- formula string -> error message (broken settings are not re-parsed every call)
local astCount, compileCount = 0, 0
local nextCompiledID = 0
local memoInserts = 0
local active = {}            -- recursion guard: source memo key -> true while that lookup is running
local guardTrips = 0         -- bumped whenever the recursion guard refuses a re-entry (taints memoisation)
local nestedEvals = 0        -- current depth of nested Evaluate calls
local warnedSources = {}     -- source name -> true once an error has been reported in chat
local warnedFormulas = {}    -- settings formula string -> true once an error has been reported in chat
local sourceListText         -- lazily built, comma-separated list of known source names

-- ----------------------------------------------------------------------------
-- Tokenizer
-- ----------------------------------------------------------------------------
local function isIdentChar(ch)
	return ch ~= "" and strfind(ch, "^[%w_]") ~= nil
end

-- Reads a money literal whose first number is `value` and whose first unit letter sits at `unitPos`.
-- Returns copper, nextPos | nil, err.
local function readMoney(str, startPos, value, unitPos)
	local copper, lastRank = 0, 4
	local partValue, unit, cur = value, strlower(strsub(str, unitPos, unitPos)), unitPos + 1
	while true do
		local rank = UNIT_RANK[unit]
		if rank >= lastRank then
			return nil, strformat("Money literal at position %d must list gold, silver and copper in that order, each at most once (e.g. 1g2s3c)", startPos)
		end
		lastRank = rank
		copper = copper + partValue * UNIT_MULT[unit]
		local ps, pe, pStr = strfind(str, "^(%d+%.?%d*)", cur)
		if not ps then
			break
		end
		local u = strlower(strsub(str, pe + 1, pe + 1))
		if not UNIT_MULT[u] then
			return nil, strformat("Expected g, s or c after '%s' in the money literal at position %d", pStr, startPos)
		end
		partValue, unit, cur = tonumber(pStr), u, pe + 2
	end
	if isIdentChar(strsub(str, cur, cur)) then
		return nil, strformat("Unexpected '%s' after the money literal at position %d", strmatch(str, "^[%w_]+", cur), startPos)
	end
	return floor(copper + 0.5), cur
end

--- Splits a formula into tokens: array of {t="num"|"id"|"op"|"lp"|"rp"|"comma"|"pct", v=..., pos=, raw=} with tokens.n set; nil, err on failure.
function Parser.Tokenize(str)
	if type(str) ~= "string" then
		return nil, "Formula must be a string"
	end
	local tokens, n = {}, 0
	local pos, len = 1, #str
	while pos <= len do
		local ws, we = strfind(str, "^%s+", pos)
		if ws then
			pos = we + 1
		else
			local start = pos
			local ch = strsub(str, pos, pos)
			local tok
			if strfind(ch, "^[%d%.]") then
				local ns, ne, numStr = strfind(str, "^(%d+%.?%d*)", pos)
				if not ns then
					ns, ne, numStr = strfind(str, "^(%.%d+)", pos)
				end
				if not ns then
					return nil, strformat("Unexpected '.' at position %d", pos)
				end
				local value = tonumber(numStr)
				if not value then
					return nil, strformat("Invalid number '%s' at position %d", numStr, pos)
				end
				local nextCh = strlower(strsub(str, ne + 1, ne + 1))
				if UNIT_MULT[nextCh] then
					local copper, after = readMoney(str, pos, value, ne + 1)
					if not copper then
						return nil, after
					end
					tok = { t = "num", v = copper }
					pos = after
				elseif nextCh == "%" then
					tok = { t = "pct", v = value / 100 }
					pos = ne + 2
				elseif isIdentChar(nextCh) then
					return nil, strformat("Unexpected '%s' after the number %s at position %d (money literals look like 5g, 20s, 10c or 1g50s)", strmatch(str, "^[%w_]+", ne + 1), numStr, pos)
				else
					tok = { t = "num", v = value }
					pos = ne + 1
				end
			elseif strfind(ch, "^[%a_]") then
				local _, ie, word = strfind(str, "^([%a_][%w_]*)", pos)
				word = strlower(word)
				if word == "item" and strsub(str, ie + 1, ie + 1) == ":" then
					local _, de, digits = strfind(str, "^(%d+)", ie + 2)
					if not de then
						return nil, strformat("Expected an item ID after 'item:' at position %d", pos)
					end
					tok = { t = "num", v = tonumber(digits), item = true }
					pos = de + 1
				else
					tok = { t = "id", v = word }
					pos = ie + 1
				end
			elseif ch == "|" then
				local _, le, id = strfind(str, "^|c[^|]*|Hitem:(%d+)[^|]*|h%[[^%]]*%]|h|r", pos)
				if not le then
					_, le, id = strfind(str, "^|Hitem:(%d+)[^|]*|h%[[^%]]*%]|h", pos)
				end
				if not le then
					return nil, strformat("Unexpected '|' at position %d (only item links may be pasted into a formula)", pos)
				end
				tok = { t = "num", v = tonumber(id), item = true }
				pos = le + 1
			elseif OPS[ch] then
				tok = { t = "op", v = ch }
				pos = pos + 1
			elseif ch == "(" then
				tok = { t = "lp", v = ch }
				pos = pos + 1
			elseif ch == ")" then
				tok = { t = "rp", v = ch }
				pos = pos + 1
			elseif ch == "," then
				tok = { t = "comma", v = ch }
				pos = pos + 1
			elseif ch == "%" then
				return nil, strformat("Unexpected '%%' at position %d (percentages are written after a number, e.g. 150%%)", pos)
			else
				return nil, strformat("Unexpected character '%s' at position %d", ch, pos)
			end
			tok.pos = start
			tok.raw = strsub(str, start, pos - 1)
			n = n + 1
			tokens[n] = tok
		end
	end
	tokens.n = n
	return tokens
end

-- ----------------------------------------------------------------------------
-- Parser (precedence climbing)
--   expr    := mul (('+'|'-') mul)*
--   mul     := unary (('*'|'/') unary)*
--   unary   := ('-'|'+') unary | power
--   power   := primary ('^' unary)?         -- right associative, binds tighter than unary minus
--   primary := num | pct [unary] | '(' expr ')' | func '(' args ')' | source ['(' itemID ')']
-- ----------------------------------------------------------------------------
local function sourceList()
	if not sourceListText then
		sourceListText = tconcat(KNOWN_SOURCE_ORDER, ", ")
	end
	return sourceListText
end

local function fail(msg, ...)
	if select("#", ...) > 0 then
		msg = strformat(msg, ...)
	end
	error(msg, 0)
end

local function describe(tok)
	if not tok then
		return "the end of the formula"
	end
	return "'" .. tok.raw .. "'"
end

local function arityText(lo, hi)
	if not hi then
		return strformat("at least %d argument%s", lo, lo == 1 and "" or "s")
	end
	if lo == hi then
		return strformat("exactly %d argument%s", lo, lo == 1 and "" or "s")
	end
	return strformat("%d to %d arguments", lo, hi)
end

-- Finds a known name that shares a prefix with an unknown identifier (for error hints).
local function suggest(name)
	local prefix = strsub(name, 1, 4)
	if #prefix < 3 then
		return nil
	end
	for i = 1, #KNOWN_SOURCE_ORDER do
		local cand = KNOWN_SOURCE_ORDER[i]
		if strsub(cand, 1, #prefix) == prefix or strfind(name, cand, 1, true) == 1 then
			return cand
		end
	end
	for fname in pairs(FUNC_ARITY) do
		if strsub(fname, 1, #prefix) == prefix then
			return fname
		end
	end
	return nil
end

local parseExpr, parseUnary

local function peek(st)
	return st.tokens[st.i]
end

local function advance(st)
	local tok = st.tokens[st.i]
	st.i = st.i + 1
	return tok
end

local function isOp(tok, op)
	return tok ~= nil and tok.t == "op" and tok.v == op
end

local function enter(st)
	st.depth = st.depth + 1
	if st.depth > MAX_DEPTH then
		fail("Formula is nested too deeply (maximum %d levels)", MAX_DEPTH)
	end
end

local function leave(st)
	st.depth = st.depth - 1
end

-- Parses "a, b, c)" after the opening parenthesis of a function call.
local function parseArgs(st, name, openTok)
	local args, n = {}, 0
	local first = peek(st)
	if first and first.t == "rp" then
		advance(st)
		args.n = 0
		return args
	end
	while true do
		n = n + 1
		args[n] = parseExpr(st)
		local tok = peek(st)
		if not tok then
			fail("Missing ')' to close '%s(' opened at position %d", name, openTok.pos)
		elseif tok.t == "comma" then
			advance(st)
		elseif tok.t == "rp" then
			advance(st)
			break
		else
			fail("Unexpected %s at position %d inside %s(...); expected ',' or ')'", describe(tok), tok.pos, name)
		end
	end
	args.n = n
	return args
end

local function parsePrimary(st)
	local tok = advance(st)
	if not tok then
		fail("Unexpected end of formula; expected a number, a price source or '('")
	end
	local t = tok.t
	if t == "num" then
		if tok.item then
			fail("Item '%s' at position %d can only be used as a price source argument, e.g. dbmarket(%s)", tok.raw, tok.pos, tok.raw)
		end
		return { k = "num", v = tok.v }
	elseif t == "pct" then
		local node = { k = "num", v = tok.v }
		local nxt = peek(st)
		if nxt and (nxt.t == "num" or nxt.t == "id" or nxt.t == "lp" or nxt.t == "pct") then
			-- prefix form: "150% crafting" == 1.5 * crafting
			enter(st)
			local operand = parseUnary(st)
			leave(st)
			return { k = "bin", op = "*", l = node, r = operand }
		end
		return node
	elseif t == "lp" then
		enter(st)
		local inner = parseExpr(st)
		leave(st)
		local close = advance(st)
		if not close or close.t ~= "rp" then
			fail("Missing ')' to close '(' opened at position %d", tok.pos)
		end
		return inner
	elseif t == "id" then
		local name = tok.v
		local nxt = peek(st)
		if FUNC_ARITY[name] then
			if not nxt or nxt.t ~= "lp" then
				fail("Function '%s' at position %d needs parentheses, e.g. %s", name, tok.pos, FUNC_USAGE[name])
			end
			advance(st)
			enter(st)
			local args = parseArgs(st, name, nxt)
			leave(st)
			local lo, hi = FUNC_ARITY[name][1], FUNC_ARITY[name][2]
			if args.n < lo or (hi and args.n > hi) then
				fail("Function '%s' at position %d takes %s, got %d (usage: %s)", name, tok.pos, arityText(lo, hi), args.n, FUNC_USAGE[name])
			end
			return { k = "call", name = name, args = args }
		elseif KNOWN_SOURCES[name] or sources[name] then
			local item
			if nxt and nxt.t == "lp" then
				advance(st)
				local arg = advance(st)
				local close = advance(st)
				if not arg or arg.t ~= "num" or (not arg.item and not strfind(arg.raw, "^%d+$")) or not close or close.t ~= "rp" then
					fail("Price source '%s' at position %d takes an optional item ID argument: %s(12345) or %s(item:12345)", name, tok.pos, name, name)
				end
				item = floor(arg.v)
				if item <= 0 then
					fail("Invalid item ID %s for price source '%s' at position %d", arg.raw, name, tok.pos)
				end
			end
			return { k = "src", name = name, item = item }
		else
			local hint = suggest(name)
			fail("Unknown identifier '%s' at position %d.%s Price sources: %s. Functions: %s", tok.raw, tok.pos, hint and strformat(" Did you mean '%s'?", hint) or "", sourceList(), FUNC_LIST)
		end
	elseif t == "rp" then
		fail("Unexpected ')' at position %d", tok.pos)
	elseif t == "comma" then
		fail("Unexpected ',' at position %d (commas only separate function arguments)", tok.pos)
	end
	fail("Unexpected operator '%s' at position %d; expected a number, a price source or '('", tok.raw, tok.pos)
end

local function parsePower(st)
	local base = parsePrimary(st)
	local tok = peek(st)
	if isOp(tok, "^") then
		advance(st)
		enter(st)
		local exponent = parseUnary(st)
		leave(st)
		return { k = "bin", op = "^", l = base, r = exponent }
	end
	return base
end

parseUnary = function(st)
	local tok = peek(st)
	if isOp(tok, "-") then
		advance(st)
		enter(st)
		local e = parseUnary(st)
		leave(st)
		if e.k == "num" then
			return { k = "num", v = -e.v }
		end
		return { k = "neg", e = e }
	elseif isOp(tok, "+") then
		advance(st)
		enter(st)
		local e = parseUnary(st)
		leave(st)
		return e
	end
	return parsePower(st)
end

local function parseMul(st)
	local left = parseUnary(st)
	local chain = 0
	while true do
		local tok = peek(st)
		if isOp(tok, "*") or isOp(tok, "/") then
			advance(st)
			chain = chain + 1
			if chain > MAX_DEPTH then
				fail("Formula chains too many operators (maximum %d in a row)", MAX_DEPTH)
			end
			local right = parseUnary(st)
			left = { k = "bin", op = tok.v, l = left, r = right }
		else
			break
		end
	end
	return left
end

parseExpr = function(st)
	local left = parseMul(st)
	local chain = 0
	while true do
		local tok = peek(st)
		if isOp(tok, "+") or isOp(tok, "-") then
			advance(st)
			chain = chain + 1
			if chain > MAX_DEPTH then
				fail("Formula chains too many operators (maximum %d in a row)", MAX_DEPTH)
			end
			local right = parseMul(st)
			left = { k = "bin", op = tok.v, l = left, r = right }
		else
			break
		end
	end
	return left
end

-- Depth of an AST (root = 1); mirrors the evaluator's depth counter exactly.
local function astDepth(node)
	local k = node.k
	if k == "bin" then
		local a, b = astDepth(node.l), astDepth(node.r)
		return 1 + (a > b and a or b)
	elseif k == "neg" then
		return 1 + astDepth(node.e)
	elseif k == "call" then
		local deepest = 0
		local args = node.args
		for i = 1, args.n do
			local d = astDepth(args[i])
			if d > deepest then
				deepest = d
			end
		end
		return 1 + deepest
	end
	return 1
end

local function parseRoot(tokens)
	local st = { tokens = tokens, i = 1, depth = 0 }
	local ast = parseExpr(st)
	local extra = peek(st)
	if extra then
		if extra.t == "rp" then
			fail("Unexpected ')' at position %d (no matching '(')", extra.pos)
		end
		fail("Unexpected %s at position %d after the end of the formula (missing an operator?)", describe(extra), extra.pos)
	end
	if astDepth(ast) > MAX_DEPTH then
		fail("Formula is nested too deeply (maximum %d levels)", MAX_DEPTH)
	end
	return ast
end

--- Parses a formula string into an AST (cached in FL.Parser.astCache[str]); returns ast | nil, err.
function Parser.Parse(str)
	if type(str) ~= "string" then
		return nil, "Formula must be a string"
	end
	local cached = astCache[str]
	if cached then
		return cached
	end
	local tokens, err = Parser.Tokenize(str)
	if not tokens then
		return nil, err
	end
	if tokens.n == 0 then
		return nil, "Formula is empty"
	end
	local ok, ast = pcall(parseRoot, tokens)
	if not ok then
		return nil, tostring(ast)
	end
	if astCount >= CACHE_LIMIT then
		wipe(astCache)
		astCount = 0
	end
	astCache[str] = ast
	astCount = astCount + 1
	return ast
end

--- Compiles a formula string into { ast = ast, id = n, src = str } (cached per string, stable id for memo keys); returns compiled | nil, err.
function Parser.Compile(str)
	if type(str) ~= "string" then
		return nil, "Formula must be a string"
	end
	local compiled = compileCache[str]
	if compiled then
		return compiled
	end
	local knownErr = compileErrors[str]
	if knownErr then
		return nil, knownErr
	end
	local ast, err = Parser.Parse(str)
	if compileCount >= CACHE_LIMIT then
		wipe(compileCache)
		wipe(compileErrors)
		compileCount = 0
	end
	compileCount = compileCount + 1
	if not ast then
		compileErrors[str] = err
		return nil, err
	end
	nextCompiledID = nextCompiledID + 1
	compiled = { ast = ast, id = nextCompiledID, src = str }
	compileCache[str] = compiled
	return compiled
end

--- Parse-only check for UI editboxes; returns ok, err.
function Parser.Validate(str)
	if type(str) ~= "string" then
		return false, "Formula must be a string"
	end
	local ast, err = Parser.Parse(str)
	if ast then
		return true
	end
	return false, err
end

-- ----------------------------------------------------------------------------
-- Evaluator
-- ----------------------------------------------------------------------------
local evalNode

local function finite(v)
	if v ~= v or v == huge or v == -huge then
		return nil
	end
	return v
end

-- Returns hit(boolean), value for a memo key valid in the current frame.
local function memoGet(key, tick, now)
	local e = memo[key]
	if e and e.tick == tick and e.time == now then
		return true, e.value
	end
	return false
end

-- Stores a memo value, reusing the entry table and sweeping stale entries occasionally.
local function memoSet(key, tick, now, value)
	local e = memo[key]
	if not e then
		memoInserts = memoInserts + 1
		if memoInserts > MEMO_SWEEP_AT then
			memoInserts = 0
			for k, old in pairs(memo) do
				if old.tick ~= tick then
					memo[k] = nil
				end
			end
		end
		e = {}
		memo[key] = e
	end
	e.tick, e.time, e.value = tick, now, value
end

local function reportSourceError(name, itemID, err)
	if not warnedSources[name] then
		warnedSources[name] = true
		FL:Warn("Price source '%s' failed for item %s: %s (further errors for this source are shown only with /fl debug)", name, tostring(itemID), tostring(err))
	else
		FL:Debug("Price source '%s' failed for item %s: %s", name, tostring(itemID), tostring(err))
	end
end

-- Looks a price source up for an item: per-frame memo, recursion guard, pcall, 0 -> nil for price sources.
local function evalSource(name, itemID, suffix)
	local fn = sources[name]
	if not fn then
		return nil
	end
	local key
	if suffix and suffix ~= 0 then
		key = name .. ":" .. (itemID or 0) .. ":" .. suffix
	else
		key = name .. ":" .. (itemID or 0)
	end
	local tick, now = FL.FrameTick or 0, GetTime()
	local hit, cached = memoGet(key, tick, now)
	if hit then
		return cached
	end
	if active[key] then
		guardTrips = guardTrips + 1
		return nil
	end
	active[key] = true
	local trips = guardTrips
	local ok, v = pcall(fn, itemID, suffix)
	active[key] = nil
	if not ok then
		reportSourceError(name, itemID, v)
		v = nil
	elseif type(v) ~= "number" then
		v = tonumber(v)
	end
	if v ~= nil then
		v = finite(v)
		if v ~= nil and v <= 0 and not ZERO_IS_VALUE[name] then
			v = nil
		end
	end
	if guardTrips == trips then
		memoSet(key, tick, now, v)
	end
	return v
end

-- Function implementations: fn(args, itemID, suffix, depth) -> number | nil
local FUNCS = {}

local function skipArg(node, v)
	return v == nil or (v == 0 and node.k == "src")
end

local function argValue(args, i, itemID, suffix, depth)
	local node = args[i]
	if not node then
		return nil
	end
	return evalNode(node, itemID, suffix, depth)
end

local function argOrZero(args, i, itemID, suffix, depth)
	local v = argValue(args, i, itemID, suffix, depth)
	if v == nil then
		return 0
	end
	return v
end

FUNCS.min = function(args, itemID, suffix, depth)
	local best
	for i = 1, args.n do
		local node = args[i]
		local v = evalNode(node, itemID, suffix, depth)
		if not skipArg(node, v) and (best == nil or v < best) then
			best = v
		end
	end
	return best
end

FUNCS.max = function(args, itemID, suffix, depth)
	local best
	for i = 1, args.n do
		local node = args[i]
		local v = evalNode(node, itemID, suffix, depth)
		if not skipArg(node, v) and (best == nil or v > best) then
			best = v
		end
	end
	return best
end

FUNCS.avg = function(args, itemID, suffix, depth)
	local sum, count = 0, 0
	for i = 1, args.n do
		local node = args[i]
		local v = evalNode(node, itemID, suffix, depth)
		if not skipArg(node, v) then
			sum = sum + v
			count = count + 1
		end
	end
	if count == 0 then
		return nil
	end
	return finite(sum / count)
end

FUNCS.first = function(args, itemID, suffix, depth)
	for i = 1, args.n do
		local v = evalNode(args[i], itemID, suffix, depth)
		if v ~= nil and v ~= 0 then
			return v
		end
	end
	return nil
end

FUNCS.check = function(args, itemID, suffix, depth)
	if argOrZero(args, 1, itemID, suffix, depth) > 0 then
		return argValue(args, 2, itemID, suffix, depth)
	end
	return argValue(args, 3, itemID, suffix, depth)
end

local function makeCompare(op)
	return function(args, itemID, suffix, depth)
		local a = argOrZero(args, 1, itemID, suffix, depth)
		local b = argOrZero(args, 2, itemID, suffix, depth)
		local result
		if op == "gt" then
			result = a > b
		elseif op == "gte" then
			result = a >= b
		elseif op == "lt" then
			result = a < b
		elseif op == "lte" then
			result = a <= b
		else
			result = a == b
		end
		if result then
			return argValue(args, 3, itemID, suffix, depth)
		end
		return argValue(args, 4, itemID, suffix, depth)
	end
end

FUNCS.ifgt = makeCompare("gt")
FUNCS.ifgte = makeCompare("gte")
FUNCS.iflt = makeCompare("lt")
FUNCS.iflte = makeCompare("lte")
FUNCS.ifeq = makeCompare("eq")

local function makeRounder(mode)
	return function(args, itemID, suffix, depth)
		local x = argValue(args, 1, itemID, suffix, depth)
		if x == nil then
			return nil
		end
		local digits = argValue(args, 2, itemID, suffix, depth) or 0
		digits = floor(digits)
		if digits > MAX_ROUND_DIGITS then
			digits = MAX_ROUND_DIGITS
		elseif digits < -MAX_ROUND_DIGITS then
			digits = -MAX_ROUND_DIGITS
		end
		local scale, scaled
		if digits >= 0 then
			scale = 10 ^ digits
			scaled = x * scale
		else
			scale = 10 ^ (-digits)
			scaled = x / scale
		end
		if mode == "up" then
			scaled = ceil(scaled)
		elseif mode == "down" then
			scaled = floor(scaled)
		else
			scaled = floor(scaled + 0.5)
		end
		if digits >= 0 then
			return finite(scaled / scale)
		end
		return finite(scaled * scale)
	end
end

FUNCS.round = makeRounder("nearest")
FUNCS.roundup = makeRounder("up")
FUNCS.rounddown = makeRounder("down")

FUNCS.abs = function(args, itemID, suffix, depth)
	local x = argValue(args, 1, itemID, suffix, depth)
	if x == nil then
		return nil
	end
	return mabs(x)
end

FUNCS.sqrt = function(args, itemID, suffix, depth)
	local x = argValue(args, 1, itemID, suffix, depth)
	if x == nil or x < 0 then
		return nil
	end
	return msqrt(x)
end

-- Recursive AST walk. Throws (caught by Evaluate's pcall) only for the depth guard.
evalNode = function(node, itemID, suffix, depth)
	if depth > MAX_DEPTH then
		error(strformat("Formula is nested too deeply (maximum %d levels)", MAX_DEPTH), 0)
	end
	local k = node.k
	if k == "num" then
		return node.v
	elseif k == "src" then
		if node.item then
			return evalSource(node.name, node.item, nil)
		end
		return evalSource(node.name, itemID, suffix)
	elseif k == "bin" then
		local l = evalNode(node.l, itemID, suffix, depth + 1)
		if l == nil then
			return nil
		end
		local r = evalNode(node.r, itemID, suffix, depth + 1)
		if r == nil then
			return nil
		end
		local op = node.op
		if op == "+" then
			return finite(l + r)
		elseif op == "-" then
			return finite(l - r)
		elseif op == "*" then
			return finite(l * r)
		elseif op == "/" then
			if r == 0 then
				return nil
			end
			return finite(l / r)
		elseif op == "^" then
			return finite(l ^ r)
		end
		return nil
	elseif k == "neg" then
		local v = evalNode(node.e, itemID, suffix, depth + 1)
		if v == nil then
			return nil
		end
		return -v
	elseif k == "call" then
		local handler = FUNCS[node.name]
		if not handler then
			return nil
		end
		return handler(node.args, itemID, suffix, depth + 1)
	end
	return nil
end

local function evalRoot(ast, itemID, suffix)
	return evalNode(ast, itemID, suffix, 1)
end

--- Evaluates a compiled formula (or formula string) for an item; returns number | nil (no price) and, for syntax/evaluation failures, nil, err.
function Parser.Evaluate(formula, itemID, suffix)
	local compiled
	local ft = type(formula)
	if ft == "string" then
		local err
		compiled, err = Parser.Compile(formula)
		if not compiled then
			return nil, err
		end
	elseif ft == "table" and formula.ast and formula.id then
		compiled = formula
	else
		return nil, "Evaluate expects a formula string or a compiled formula"
	end
	local it = type(itemID)
	if it == "string" then
		itemID = tonumber(itemID) or (FL.ItemIDFromLink and FL.ItemIDFromLink(itemID)) or nil
	elseif it ~= "number" then
		itemID = nil
	end
	if suffix ~= nil then
		suffix = tonumber(suffix)
	end
	local key = compiled.id .. ":" .. (itemID or 0) .. ":" .. (suffix or 0)
	local tick, now = FL.FrameTick or 0, GetTime()
	local hit, cached = memoGet(key, tick, now)
	if hit then
		return cached
	end
	if nestedEvals >= MAX_NESTED_EVAL then
		return nil, strformat("Formula recursion too deep (more than %d formulas nested through postmin/postmax/crafting)", MAX_NESTED_EVAL)
	end
	nestedEvals = nestedEvals + 1
	local trips = guardTrips
	local ok, value = pcall(evalRoot, compiled.ast, itemID, suffix)
	nestedEvals = nestedEvals - 1
	if not ok then
		return nil, tostring(value)
	end
	if guardTrips == trips then
		memoSet(key, tick, now, value)
	end
	return value
end

--- Registers (or replaces) a price source: fn(itemID, suffix) -> number | nil. Names are case-insensitive identifiers; returns true on success.
function Parser.RegisterSource(name, fn)
	if type(name) ~= "string" or not strfind(name, "^[%a_][%w_]*$") then
		FL:Warn("Parser.RegisterSource: '%s' is not a valid source name (letters, digits and underscores, starting with a letter)", tostring(name))
		return false
	end
	if type(fn) ~= "function" then
		FL:Warn("Parser.RegisterSource('%s'): second argument must be a function", name)
		return false
	end
	name = strlower(name)
	if FUNC_ARITY[name] then
		FL:Warn("Parser.RegisterSource('%s'): name collides with a built-in function", name)
		return false
	end
	sources[name] = fn
	if not KNOWN_SOURCES[name] then
		KNOWN_SOURCES[name] = true
		KNOWN_SOURCE_ORDER[#KNOWN_SOURCE_ORDER + 1] = name
		sourceListText = nil
		-- formulas that failed on this identifier before may parse now
		wipe(compileErrors)
	end
	wipe(memo)
	memoInserts = 0
	return true
end

--- Drops every cached AST, compiled formula and memo entry (sources stay registered).
function Parser.ClearCache()
	wipe(astCache)
	wipe(compileCache)
	wipe(compileErrors)
	wipe(memo)
	astCount, compileCount, memoInserts = 0, 0, 0
end

-- ----------------------------------------------------------------------------
-- Base price sources
--   dbmarket, dbregionmarket, dbminbuyout, dbhistorical, numauctions, dbsalerate,
--   vendorsell, vendorbuy, matprice, undercut, postmin, postmax, restocktarget
-- AdvancedFeatures.lua registers crafting, avgbuy, avgsell and inventory later.
-- ----------------------------------------------------------------------------
local function getSettings()
	return FL.Settings or (FL.RuntimeDB and FL.RuntimeDB.settings) or FL.DefaultSettings
end

local function marketField(itemID, field, suffix)
	local Market = FL.Market
	if Market and Market.Get then
		return Market.Get(itemID, field, suffix)
	end
	return nil
end

-- Reads one field of the vendor table row for an item (nil when missing or not positive).
local function vendorRow(itemID, field)
	local db = FL.DB and FL.DB.vendor
	if not db then
		return nil
	end
	local rowID = db:FindFirst("itemID", itemID)
	if not rowID then
		return nil
	end
	local v = db:Get(rowID, field)
	if type(v) == "number" and v > 0 then
		return v
	end
	return nil
end

-- Converts a money setting ("1c", "5s", "1g50s", "150" or a number) to copper; `default` when unparseable.
local function moneyFromSetting(v, default)
	if type(v) == "number" then
		return v
	end
	if type(v) == "string" and v ~= "" then
		local copper = FL.ParseMoney and FL.ParseMoney(v)
		if type(copper) ~= "number" then
			copper = Parser.Evaluate(v)
		end
		if type(copper) == "number" then
			return copper
		end
	end
	return default
end

-- Evaluates a formula stored in settings[section][field] for an item; reports a broken formula once.
local function evalSettingFormula(section, field, itemID, suffix)
	local s = getSettings()
	local sec = s and s[section]
	local formula = sec and sec[field]
	if type(formula) ~= "string" or formula == "" then
		return nil
	end
	local value, err = Parser.Evaluate(formula, itemID, suffix)
	if err and not warnedFormulas[formula] then
		warnedFormulas[formula] = true
		FL:Warn("settings.%s.%s formula error: %s", section, field, err)
	end
	return value
end

local function srcMarketValue(itemID, suffix)
	if not itemID then
		return nil
	end
	return marketField(itemID, "marketValue", suffix)
end

local function srcMinBuyout(itemID, suffix)
	if not itemID then
		return nil
	end
	local Posting = FL.Posting
	if Posting and Posting.currentMin then
		local override = Posting.currentMin[itemID]
		if type(override) == "number" and override > 0 then
			return override
		end
	end
	return marketField(itemID, "minBuyout", suffix)
end

local function srcHistorical(itemID, suffix)
	if not itemID then
		return nil
	end
	return marketField(itemID, "historical", suffix)
end

local function srcNumAuctions(itemID, suffix)
	if not itemID then
		return nil
	end
	return marketField(itemID, "numAuctions", suffix)
end

local function srcSaleRate(itemID, suffix)
	if not itemID then
		return nil
	end
	return marketField(itemID, "soldPerDay", suffix)
end

local function srcVendorSell(itemID)
	if not itemID then
		return nil
	end
	local v
	local Vendor = FL.Vendor
	if Vendor and Vendor.SellPrice then
		v = Vendor.SellPrice(itemID)
	end
	if (type(v) ~= "number" or v <= 0) and FL.GetItemSellPrice then
		v = FL.GetItemSellPrice(itemID)
	end
	if type(v) ~= "number" or v <= 0 then
		v = vendorRow(itemID, "sellPrice")
	end
	return v
end

local function srcVendorBuy(itemID)
	if not itemID then
		return nil
	end
	local v
	local Vendor = FL.Vendor
	if Vendor and Vendor.BuyPrice then
		v = Vendor.BuyPrice(itemID)
	end
	if type(v) ~= "number" or v <= 0 then
		v = vendorRow(itemID, "buyPrice")
	end
	return v
end

-- matprice = min(vendorbuy, first(dbminbuyout, dbmarket)) with unavailable parts skipped.
local function srcMatPrice(itemID, suffix)
	if not itemID then
		return nil
	end
	local vendor = evalSource("vendorbuy", itemID, suffix)
	local ah = evalSource("dbminbuyout", itemID, suffix)
	if not ah then
		ah = evalSource("dbmarket", itemID, suffix)
	end
	if vendor then
		if ah and ah < vendor then
			return ah
		end
		return vendor
	end
	return ah
end

local function srcUndercut()
	local s = getSettings()
	local posting = s and s.posting
	local defaults = FL.DefaultSettings and FL.DefaultSettings.posting
	local fallback = moneyFromSetting(defaults and defaults.undercut, 1)
	return moneyFromSetting(posting and posting.undercut, fallback)
end

local function srcPostMin(itemID, suffix)
	if not itemID then
		return nil
	end
	return evalSettingFormula("posting", "minFormula", itemID, suffix)
end

local function srcPostMax(itemID, suffix)
	if not itemID then
		return nil
	end
	return evalSettingFormula("posting", "maxFormula", itemID, suffix)
end

local function srcRestockTarget()
	local s = getSettings()
	local crafting = s and s.crafting
	local target = crafting and tonumber(crafting.restockTarget)
	if target == nil then
		local defaults = FL.DefaultSettings and FL.DefaultSettings.crafting
		target = defaults and tonumber(defaults.restockTarget) or 0
	end
	return target
end

Parser.RegisterSource("dbmarket", srcMarketValue)
Parser.RegisterSource("dbregionmarket", srcMarketValue)
Parser.RegisterSource("dbminbuyout", srcMinBuyout)
Parser.RegisterSource("dbhistorical", srcHistorical)
Parser.RegisterSource("numauctions", srcNumAuctions)
Parser.RegisterSource("dbsalerate", srcSaleRate)
Parser.RegisterSource("vendorsell", srcVendorSell)
Parser.RegisterSource("vendorbuy", srcVendorBuy)
Parser.RegisterSource("matprice", srcMatPrice)
Parser.RegisterSource("undercut", srcUndercut)
Parser.RegisterSource("postmin", srcPostMin)
Parser.RegisterSource("postmax", srcPostMax)
Parser.RegisterSource("restocktarget", srcRestockTarget)
