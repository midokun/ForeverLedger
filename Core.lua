local addonName, FL = ...
--------------------------------------------------------------------------------
-- ForeverLedger / Core.lua
-- Identity, chat output, utilities, asynchronous item cache, event and signal
-- dispatch, timers, frame tick, serializer, cold-start safeguard persistence,
-- hardware-event secure dispatcher and slash commands.
-- Loaded first: nothing here calls into later files at file scope.
--------------------------------------------------------------------------------
_G["ForeverLedger"] = FL

--------------------------------------------------------------------------------
-- Cached globals
--------------------------------------------------------------------------------
local _G = _G
local pairs, ipairs, type, tonumber, tostring = pairs, ipairs, type, tonumber, tostring
local select, pcall, error, next = select, pcall, error, next
local floor, abs, huge = math.floor, math.abs, math.huge
local format, strsub, strbyte, strchar, strfind, strmatch, gsub, lower, strlen =
	string.format, string.sub, string.byte, string.char, string.find, string.match, string.gsub, string.lower, string.len
local tremove, tconcat, tsort = table.remove, table.concat, table.sort
local wipe, strtrim = wipe, strtrim
local time, date, GetTime = time, date, GetTime
local CreateFrame, UIParent, GameTooltip = CreateFrame, UIParent, GameTooltip
local InCombatLockdown = InCombatLockdown
local GetBuildInfo, GetRealmName, GetNormalizedRealmName = GetBuildInfo, GetRealmName, GetNormalizedRealmName
local UnitName, UnitFactionGroup = UnitName, UnitFactionGroup
local issecretvalue = issecretvalue
local C_Item, C_Timer, C_AddOns, Item = C_Item, C_Timer, C_AddOns, Item
local GetAddOnMetadata = GetAddOnMetadata
local DEFAULT_CHAT_FRAME = DEFAULT_CHAT_FRAME

--------------------------------------------------------------------------------
-- Identity
--------------------------------------------------------------------------------
FL.name = addonName or "ForeverLedger"

local metaVersion
if C_AddOns and C_AddOns.GetAddOnMetadata then
	local ok, v = pcall(C_AddOns.GetAddOnMetadata, FL.name, "Version")
	if ok then metaVersion = v end
elseif GetAddOnMetadata then
	local ok, v = pcall(GetAddOnMetadata, FL.name, "Version")
	if ok then metaVersion = v end
end
FL.version = (type(metaVersion) == "string" and metaVersion ~= "" and metaVersion) or "dev"

local clientVersion, clientBuild, clientDate, clientToc = GetBuildInfo()
FL.buildNumber = tonumber(clientBuild) or 0
FL.tocVersion = tonumber(clientToc) or 0
FL.clientVersion = tostring(clientVersion or "?")
FL.clientDate = tostring(clientDate or "?")
FL.isForever = (WOW_PROJECT_CAMELOT ~= nil and WOW_PROJECT_ID == WOW_PROJECT_CAMELOT)
	or (FL.tocVersion >= 16000 and FL.tocVersion < 20000)

FL.playerKey = "Unknown"
FL.realmKey = "Unknown"
FL.factionKey = "Neutral"
FL.marketKey = "Unknown-Neutral"
FL.coldStartEmpty = false
FL.hydrated = false
FL.dbReady = false
FL.RuntimeDB = nil
FL.CharDB = nil
FL.Settings = nil

-- Returns a unit-API string only when it is a real, non-secret string.
local function safeUnitValue(v)
	if v == nil then return nil end
	if issecretvalue and issecretvalue(v) then return nil end
	if type(v) ~= "string" or v == "" then return nil end
	return v
end

-- Resolves playerKey / realmKey / factionKey / marketKey from the client.
local function resolveIdentity()
	local realm
	if GetRealmName then
		local ok, v = pcall(GetRealmName)
		if ok then realm = v end
	end
	if (type(realm) ~= "string" or realm == "") and GetNormalizedRealmName then
		local ok, v = pcall(GetNormalizedRealmName)
		if ok then realm = v end
	end
	FL.realmKey = (type(realm) == "string" and realm ~= "" and realm) or "Unknown"
	local name
	if UnitName then
		local ok, v = pcall(UnitName, "player")
		if ok then name = safeUnitValue(v) end
	end
	FL.playerKey = (name or "Unknown") .. "-" .. FL.realmKey
	local faction
	if UnitFactionGroup then
		local ok, v = pcall(UnitFactionGroup, "player")
		if ok then faction = safeUnitValue(v) end
	end
	if faction ~= "Alliance" and faction ~= "Horde" then faction = "Neutral" end
	FL.factionKey = faction
	FL.marketKey = FL.realmKey .. "-" .. FL.factionKey
end

--------------------------------------------------------------------------------
-- Chat output
--------------------------------------------------------------------------------
local CHAT_PREFIX = "|cff33ff99ForeverLedger|r: "

local function formatMessage(fmt, ...)
	if select("#", ...) > 0 then
		local ok, s = pcall(format, tostring(fmt), ...)
		if ok then return s end
		return tostring(fmt)
	end
	return tostring(fmt)
end

local function chatMessage(text)
	if DEFAULT_CHAT_FRAME and DEFAULT_CHAT_FRAME.AddMessage then
		DEFAULT_CHAT_FRAME:AddMessage(text)
	end
end

-- Prints a prefixed chat message; string.format is applied when extra args are given.
function FL.Print(self, fmt, ...)
	if self ~= FL then return FL.Print(FL, self, fmt, ...) end
	chatMessage(CHAT_PREFIX .. formatMessage(fmt, ...))
end

-- Prints a prefixed, red-tinted warning message.
function FL.Warn(self, fmt, ...)
	if self ~= FL then return FL.Warn(FL, self, fmt, ...) end
	chatMessage(CHAT_PREFIX .. "|cffff4040" .. formatMessage(fmt, ...) .. "|r")
end

-- Prints a grey debug message, only when settings.debug is enabled.
function FL.Debug(self, fmt, ...)
	if self ~= FL then return FL.Debug(FL, self, fmt, ...) end
	local root = FL.RuntimeDB
	if root and root.settings and root.settings.debug then
		chatMessage(CHAT_PREFIX .. "|cff999999[debug] " .. formatMessage(fmt, ...) .. "|r")
	end
end

-- Reports an error thrown by a handler, suppressing repeats of the same message after 3 prints.
local errorCounts = {}
local function reportHandlerError(where, err)
	local key = tostring(err)
	local n = (errorCounts[key] or 0) + 1
	errorCounts[key] = n
	if n <= 3 then
		FL:Warn("%s error: %s%s", where, key, (n == 3) and " (further repeats suppressed)" or "")
	end
end

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------
local function deepCopyInner(src, seen)
	if type(src) ~= "table" then return src end
	local existing = seen[src]
	if existing then return existing end
	local dst = {}
	seen[src] = dst
	for k, v in pairs(src) do
		dst[deepCopyInner(k, seen)] = deepCopyInner(v, seen)
	end
	return dst
end

-- Recursive deep copy that handles cycles and shared references; non-tables are returned as-is.
function FL.DeepCopy(src)
	if type(src) ~= "table" then return src end
	return deepCopyInner(src, {})
end

-- Rounds to the nearest integer (halves away from zero).
function FL.Round(n)
	n = tonumber(n) or 0
	if n ~= n then return 0 end
	if n >= 0 then return floor(n + 0.5) end
	return -floor(-n + 0.5)
end

local GOLD_COLOR, SILVER_COLOR, COPPER_COLOR = "|cffffd70a", "|cffc7c7cf", "|cffeda55f"
local moneyParts = {}

-- Formats copper as "12g 34s 56c" with colour escapes; zero parts omitted, "0c" for zero, negatives supported.
function FL.FormatMoney(copper, noColor)
	copper = FL.Round(copper)
	local negative = copper < 0
	if negative then copper = -copper end
	local g = floor(copper / 10000)
	local s = floor((copper - g * 10000) / 100)
	local c = copper - g * 10000 - s * 100
	local n = 0
	if g > 0 then
		n = n + 1
		moneyParts[n] = noColor and (g .. "g") or (GOLD_COLOR .. g .. "g|r")
	end
	if s > 0 then
		n = n + 1
		moneyParts[n] = noColor and (s .. "s") or (SILVER_COLOR .. s .. "s|r")
	end
	if c > 0 or n == 0 then
		n = n + 1
		moneyParts[n] = noColor and (c .. "c") or (COPPER_COLOR .. c .. "c|r")
	end
	local out = tconcat(moneyParts, " ", 1, n)
	if negative then out = "-" .. out end
	return out
end

-- Parses "1g2s3c" / "5s" / "1.5g" / "150" (plain copper) into copper, or nil when malformed.
function FL.ParseMoney(str)
	if type(str) == "number" then
		if str ~= str then return nil end
		return floor(str)
	end
	if type(str) ~= "string" then return nil end
	local s = lower((gsub(str, "%s+", "")))
	if s == "" then return nil end
	local negative = false
	if strsub(s, 1, 1) == "-" then
		negative = true
		s = strsub(s, 2)
	end
	if s == "" then return nil end
	local total
	local plain = tonumber(s)
	if plain then
		if plain ~= plain then return nil end
		total = floor(plain)
	else
		total = 0
		local pos, len = 1, strlen(s)
		while pos <= len do
			local a, b, num, unit = strfind(s, "^(%d+%.?%d*)([gsc])", pos)
			if not a then return nil end
			local value = tonumber(num)
			if not value then return nil end
			if unit == "g" then
				total = total + value * 10000
			elseif unit == "s" then
				total = total + value * 100
			else
				total = total + value
			end
			pos = b + 1
		end
		total = floor(total + 0.5)
	end
	if negative then total = -total end
	return total
end

-- Extracts the item ID from an item link or "item:ID" string (numbers pass through).
function FL.ItemIDFromLink(link)
	if type(link) == "number" then return link end
	if type(link) ~= "string" then return nil end
	local id = strmatch(link, "item:(%d+)")
	if id then return tonumber(id) end
	return nil
end

-- Returns the suffix ID (8th colon field) of an item link, 0 when absent.
function FL.ItemSuffixFromLink(link)
	if type(link) ~= "string" then return 0 end
	local suffix = strmatch(link, "item:[^:|]*:[^:|]*:[^:|]*:[^:|]*:[^:|]*:[^:|]*:(%-?%d+)")
	return tonumber(suffix) or 0
end

--------------------------------------------------------------------------------
-- Event dispatch (one hidden frame, many handlers per event)
--------------------------------------------------------------------------------
local eventFrame = CreateFrame("Frame")
local eventHandlers = {}
local dispatchScratch = {}
local dispatchDepth = 0

-- Calls every handler in list with (name, ...); tolerant of handlers removing themselves mid-dispatch.
local function dispatchList(list, where, name, ...)
	dispatchDepth = dispatchDepth + 1
	local scratch = dispatchScratch[dispatchDepth]
	if not scratch then
		scratch = {}
		dispatchScratch[dispatchDepth] = scratch
	end
	local n = #list
	for i = 1, n do scratch[i] = list[i] end
	for i = 1, n do
		local ok, err = pcall(scratch[i], name, ...)
		if not ok then reportHandlerError(where .. " " .. tostring(name), err) end
	end
	for i = 1, n do scratch[i] = nil end
	dispatchDepth = dispatchDepth - 1
end

-- Registers handler(event, ...) for a game event; the frame registers the event on demand.
function FL.RegisterEvent(event, handler)
	if type(event) ~= "string" or type(handler) ~= "function" then return false end
	local list = eventHandlers[event]
	if not list then
		local ok = pcall(eventFrame.RegisterEvent, eventFrame, event)
		if not ok then
			FL:Debug("Unknown event %s", event)
			return false
		end
		list = {}
		eventHandlers[event] = list
	end
	for i = 1, #list do
		if list[i] == handler then return true end
	end
	list[#list + 1] = handler
	return true
end

-- Removes a handler; the game event is unregistered when the last handler goes away.
function FL.UnregisterEvent(event, handler)
	local list = eventHandlers[event]
	if not list then return false end
	for i = #list, 1, -1 do
		if list[i] == handler then tremove(list, i) end
	end
	if #list == 0 then
		eventHandlers[event] = nil
		pcall(eventFrame.UnregisterEvent, eventFrame, event)
	end
	return true
end

eventFrame:SetScript("OnEvent", function(self, event, ...)
	local list = eventHandlers[event]
	if list then dispatchList(list, "Event", event, ...) end
end)

--------------------------------------------------------------------------------
-- Internal signals (pub/sub)
--------------------------------------------------------------------------------
local signalHandlers = {}

-- Subscribes fn(signal, ...) to an internal signal such as "FL_MARKET_UPDATED".
function FL.On(signal, fn)
	if type(signal) ~= "string" or type(fn) ~= "function" then return false end
	local list = signalHandlers[signal]
	if not list then
		list = {}
		signalHandlers[signal] = list
	end
	for i = 1, #list do
		if list[i] == fn then return true end
	end
	list[#list + 1] = fn
	return true
end

-- Unsubscribes fn from a signal.
function FL.Off(signal, fn)
	local list = signalHandlers[signal]
	if not list then return false end
	for i = #list, 1, -1 do
		if list[i] == fn then tremove(list, i) end
	end
	if #list == 0 then signalHandlers[signal] = nil end
	return true
end

-- Fires a signal to every subscriber (each call protected).
function FL.Fire(signal, ...)
	local list = signalHandlers[signal]
	if list then dispatchList(list, "Signal", signal, ...) end
end

--------------------------------------------------------------------------------
-- Timers (protected wrappers around C_Timer)
--------------------------------------------------------------------------------
FL.Timer = {}

-- Runs fn once after sec seconds; errors are reported through FL:Warn instead of propagating.
function FL.Timer.After(sec, fn)
	if type(fn) ~= "function" then return false end
	sec = tonumber(sec) or 0
	if sec < 0 then sec = 0 end
	if not (C_Timer and C_Timer.After) then
		local ok, err = pcall(fn)
		if not ok then reportHandlerError("Timer", err) end
		return true
	end
	C_Timer.After(sec, function()
		local ok, err = pcall(fn)
		if not ok then reportHandlerError("Timer", err) end
	end)
	return true
end

-- Creates a repeating ticker calling fn(ticker) every sec seconds; returns the ticker (:Cancel()).
function FL.Timer.NewTicker(sec, fn, iterations)
	if type(fn) ~= "function" then return nil end
	if not (C_Timer and C_Timer.NewTicker) then return nil end
	sec = tonumber(sec) or 1
	if sec < 0.01 then sec = 0.01 end
	return C_Timer.NewTicker(sec, function(ticker)
		local ok, err = pcall(fn, ticker)
		if not ok then reportHandlerError("Ticker", err) end
	end, iterations)
end

--------------------------------------------------------------------------------
-- Frame tick (one increment per rendered frame)
--------------------------------------------------------------------------------
FL.FrameTick = 0
local tickFrame = CreateFrame("Frame")
tickFrame:SetScript("OnUpdate", function()
	FL.FrameTick = FL.FrameTick + 1
end)

--------------------------------------------------------------------------------
-- Item information cache (C_Item data is asynchronous until cached)
--------------------------------------------------------------------------------
local GetItemInfoAPI = (C_Item and C_Item.GetItemInfo) or GetItemInfo
local GetItemInfoInstantAPI = (C_Item and C_Item.GetItemInfoInstant) or GetItemInfoInstant
local RequestLoadItemDataByID = C_Item and C_Item.RequestLoadItemDataByID

local itemNameCache, itemLinkCache, itemQualityCache, itemSellCache = {}, {}, {}, {}
local itemCallbacks = {}
local itemPendingSince = {}
local itemPendingCount = 0
local itemSweepTicker = nil
local itemLoadEventRegistered = false
local ITEM_LOAD_TIMEOUT = 15
local ITEM_SWEEP_INTERVAL = 5

-- Reads C_Item.GetItemInfo into the local caches; false when the item is not cached yet.
local function cacheItem(itemID)
	if not GetItemInfoAPI then return false end
	local name, link, quality, _, _, _, _, _, _, _, sellPrice = GetItemInfoAPI(itemID)
	if not name then return false end
	itemNameCache[itemID] = name
	itemLinkCache[itemID] = link
	itemQualityCache[itemID] = quality or 1
	itemSellCache[itemID] = sellPrice or 0
	return true
end

-- Completes a pending load: fills caches and runs every waiting callback as callback(itemID, cached).
local function finishItemLoad(itemID, success)
	local list = itemCallbacks[itemID]
	itemCallbacks[itemID] = nil
	if itemPendingSince[itemID] then
		itemPendingSince[itemID] = nil
		itemPendingCount = itemPendingCount - 1
	end
	if success ~= false and not itemNameCache[itemID] then cacheItem(itemID) end
	local cached = itemNameCache[itemID] ~= nil
	if list then
		for i = 1, #list do
			local ok, err = pcall(list[i], itemID, cached)
			if not ok then reportHandlerError("Item callback", err) end
		end
	end
	if itemPendingCount <= 0 then
		itemPendingCount = 0
		if itemSweepTicker then
			itemSweepTicker:Cancel()
			itemSweepTicker = nil
		end
	end
end

local sweepExpired = {}
-- Periodic sweep that fails item loads which never answered (invalid ids, server hiccups).
local function sweepItemLoads()
	local now = GetTime()
	local n = 0
	for itemID, since in pairs(itemPendingSince) do
		if now - since > ITEM_LOAD_TIMEOUT then
			n = n + 1
			sweepExpired[n] = itemID
		end
	end
	for i = 1, n do
		finishItemLoad(sweepExpired[i], nil)
		sweepExpired[i] = nil
	end
end

local function onItemDataLoadResult(event, itemID, success)
	if itemID and (itemCallbacks[itemID] or itemPendingSince[itemID]) then
		finishItemLoad(itemID, success)
	end
end

-- Calls callback(itemID) once C_Item data is cached (immediately when it already is); dedups callbacks.
function FL.RequestItem(itemID, callback)
	itemID = tonumber(itemID)
	if not itemID or itemID <= 0 then return false end
	itemID = floor(itemID)
	if itemNameCache[itemID] or cacheItem(itemID) then
		if type(callback) == "function" then
			local ok, err = pcall(callback, itemID, true)
			if not ok then reportHandlerError("Item callback", err) end
		end
		return true
	end
	if GetItemInfoInstantAPI and not GetItemInfoInstantAPI(itemID) then
		return false
	end
	if type(callback) == "function" then
		local list = itemCallbacks[itemID]
		if not list then
			list = {}
			itemCallbacks[itemID] = list
		end
		local duplicate = false
		for i = 1, #list do
			if list[i] == callback then
				duplicate = true
				break
			end
		end
		if not duplicate then list[#list + 1] = callback end
	end
	if itemPendingSince[itemID] then return true end
	itemPendingSince[itemID] = GetTime()
	itemPendingCount = itemPendingCount + 1
	local issued = false
	if Item and Item.CreateFromItemID then
		local ok, obj = pcall(Item.CreateFromItemID, Item, itemID)
		if ok and type(obj) == "table" and obj.ContinueOnItemLoad then
			local empty = false
			if obj.IsItemEmpty then
				local okEmpty, isEmpty = pcall(obj.IsItemEmpty, obj)
				empty = okEmpty and isEmpty and true or false
			end
			if not empty then
				issued = pcall(obj.ContinueOnItemLoad, obj, function()
					finishItemLoad(itemID, true)
				end)
			end
		end
	end
	if not issued then
		if not itemLoadEventRegistered then
			itemLoadEventRegistered = true
			FL.RegisterEvent("ITEM_DATA_LOAD_RESULT", onItemDataLoadResult)
		end
		if RequestLoadItemDataByID then pcall(RequestLoadItemDataByID, itemID) end
	end
	if not itemSweepTicker and C_Timer and C_Timer.NewTicker then
		itemSweepTicker = C_Timer.NewTicker(ITEM_SWEEP_INTERVAL, sweepItemLoads)
	end
	return true
end

-- Cached item name or nil (an asynchronous load is triggered when missing).
function FL.GetItemName(itemID)
	itemID = tonumber(itemID)
	if not itemID or itemID <= 0 then return nil end
	local v = itemNameCache[itemID]
	if v then return v end
	if cacheItem(itemID) then return itemNameCache[itemID] end
	FL.RequestItem(itemID)
	return nil
end

-- Cached vendor sell price in copper or nil (asynchronous load triggered when missing).
function FL.GetItemSellPrice(itemID)
	itemID = tonumber(itemID)
	if not itemID or itemID <= 0 then return nil end
	local v = itemSellCache[itemID]
	if v then return v end
	if cacheItem(itemID) then return itemSellCache[itemID] end
	FL.RequestItem(itemID)
	return nil
end

-- Cached item quality 0..7 or nil (asynchronous load triggered when missing).
function FL.GetItemQuality(itemID)
	itemID = tonumber(itemID)
	if not itemID or itemID <= 0 then return nil end
	local v = itemQualityCache[itemID]
	if v then return v end
	if cacheItem(itemID) then return itemQualityCache[itemID] end
	FL.RequestItem(itemID)
	return nil
end

-- Cached item link or nil (asynchronous load triggered when missing).
function FL.GetItemLinkCached(itemID)
	itemID = tonumber(itemID)
	if not itemID or itemID <= 0 then return nil end
	local v = itemLinkCache[itemID]
	if v then return v end
	if cacheItem(itemID) then return itemLinkCache[itemID] end
	FL.RequestItem(itemID)
	return nil
end

--------------------------------------------------------------------------------
-- Serializer: deterministic text encoding with a recursive-descent decoder.
-- value := 'S' len ':' bytes | 'N' number ';' | 'B' ('0'|'1')
--        | 'A' value* 'E' (array 1..n) | 'T' (key value)* 'E' (sorted keys)
-- The whole string carries the prefix "FL1". No loadstring anywhere.
--------------------------------------------------------------------------------
FL.Serializer = {}
local SER_PREFIX = "FL1"
local SER_MAX_DEPTH = 128
local serTypeRank = { number = 1, string = 2, boolean = 3 }

-- Round-trip safe number text; NaN and infinities encode as 0.
local function serNumber(v)
	if v ~= v or v == huge or v == -huge then return "0" end
	if v == floor(v) and abs(v) < 1e15 then return format("%.0f", v) end
	local s = format("%.14g", v)
	if tonumber(s) ~= v then s = format("%.17g", v) end
	return s
end

local function serKeyLess(a, b)
	local ta, tb = type(a), type(b)
	if ta ~= tb then return serTypeRank[ta] < serTypeRank[tb] end
	if ta == "boolean" then return (not a) and b end
	return a < b
end

local function serEncode(v, out, depth, seen)
	local tv = type(v)
	if tv == "string" then
		out[#out + 1] = "S"
		out[#out + 1] = strlen(v)
		out[#out + 1] = ":"
		out[#out + 1] = v
	elseif tv == "number" then
		out[#out + 1] = "N"
		out[#out + 1] = serNumber(v)
		out[#out + 1] = ";"
	elseif tv == "boolean" then
		out[#out + 1] = v and "B1" or "B0"
	elseif tv == "table" then
		if depth > SER_MAX_DEPTH then error("nesting deeper than " .. SER_MAX_DEPTH) end
		if seen[v] then error("cyclic table reference") end
		seen[v] = true
		local count, maxIndex, isArray = 0, 0, true
		for k in pairs(v) do
			count = count + 1
			if isArray then
				if type(k) == "number" and k >= 1 and k == floor(k) then
					if k > maxIndex then maxIndex = k end
				else
					isArray = false
				end
			end
		end
		if isArray and maxIndex ~= count then isArray = false end
		if isArray then
			out[#out + 1] = "A"
			for i = 1, count do serEncode(v[i], out, depth + 1, seen) end
		else
			local keys, nk = {}, 0
			for k in pairs(v) do
				if not serTypeRank[type(k)] then error("unsupported key type " .. type(k)) end
				nk = nk + 1
				keys[nk] = k
			end
			tsort(keys, serKeyLess)
			out[#out + 1] = "T"
			for i = 1, nk do
				local k = keys[i]
				serEncode(k, out, depth + 1, seen)
				serEncode(v[k], out, depth + 1, seen)
			end
		end
		out[#out + 1] = "E"
		seen[v] = nil
	else
		error("unsupported value type " .. tv)
	end
end

-- Encodes a nested table (string/number/boolean keys and values) into a deterministic string.
function FL.Serializer.Encode(tbl)
	if type(tbl) ~= "table" then return nil, "Serializer: expected a table" end
	local out = { SER_PREFIX }
	local ok, err = pcall(serEncode, tbl, out, 0, {})
	if not ok then return nil, "Serializer: " .. tostring(err) end
	return tconcat(out)
end

local B_S, B_N, B_B, B_A, B_T, B_E = strbyte("S"), strbyte("N"), strbyte("B"), strbyte("A"), strbyte("T"), strbyte("E")
local B_0, B_1 = strbyte("0"), strbyte("1")

local function serDecode(str, pos, depth)
	local tag = strbyte(str, pos)
	if not tag then error("unexpected end of data at " .. pos) end
	if tag == B_S then
		local colon = strfind(str, ":", pos + 1, true)
		if not colon then error("malformed string length at " .. pos) end
		local len = tonumber(strsub(str, pos + 1, colon - 1))
		if not len or len < 0 or len ~= floor(len) then error("invalid string length at " .. pos) end
		local last = colon + len
		if last > strlen(str) then error("truncated string at " .. pos) end
		return strsub(str, colon + 1, last), last + 1
	elseif tag == B_N then
		local semi = strfind(str, ";", pos + 1, true)
		if not semi then error("malformed number at " .. pos) end
		local num = tonumber(strsub(str, pos + 1, semi - 1))
		if not num then error("invalid number at " .. pos) end
		return num, semi + 1
	elseif tag == B_B then
		local b = strbyte(str, pos + 1)
		if b == B_1 then return true, pos + 2 end
		if b == B_0 then return false, pos + 2 end
		error("invalid boolean at " .. pos)
	elseif tag == B_A then
		if depth > SER_MAX_DEPTH then error("nesting deeper than " .. SER_MAX_DEPTH) end
		local t, n = {}, 0
		pos = pos + 1
		while true do
			local b = strbyte(str, pos)
			if not b then error("unterminated array") end
			if b == B_E then return t, pos + 1 end
			local v
			v, pos = serDecode(str, pos, depth + 1)
			n = n + 1
			t[n] = v
		end
	elseif tag == B_T then
		if depth > SER_MAX_DEPTH then error("nesting deeper than " .. SER_MAX_DEPTH) end
		local t = {}
		pos = pos + 1
		while true do
			local b = strbyte(str, pos)
			if not b then error("unterminated table") end
			if b == B_E then return t, pos + 1 end
			local k, v
			k, pos = serDecode(str, pos, depth + 1)
			if type(k) == "table" then error("table used as key") end
			if k ~= k then error("NaN used as key") end
			v, pos = serDecode(str, pos, depth + 1)
			t[k] = v
		end
	end
	error("unknown tag '" .. strchar(tag) .. "' at " .. pos)
end

-- Decodes a string produced by Encode; returns table or nil, err.
function FL.Serializer.Decode(str)
	if type(str) ~= "string" then return nil, "Serializer: expected a string" end
	str = strtrim(str)
	local pos = 1
	if strsub(str, 1, 3) == SER_PREFIX then pos = 4 end
	if pos > strlen(str) then return nil, "Serializer: empty input" end
	local ok, result, nextPos = pcall(serDecode, str, pos, 0)
	if not ok then return nil, "Serializer: " .. tostring(result) end
	if type(result) ~= "table" then return nil, "Serializer: top-level value is not a table" end
	if nextPos <= strlen(str) and strfind(str, "%S", nextPos) then
		return nil, "Serializer: trailing data at position " .. nextPos
	end
	return result
end

--------------------------------------------------------------------------------
-- Settings defaults (SPEC §2.2)
--------------------------------------------------------------------------------
FL.DefaultSettings = {
	debug = false,
	minimapHint = true,
	tooltip = {
		enabled = true, showMarket = true, showMinBuyout = true, showCrafting = true, showVendor = true,
		showSaleRate = true, showInventory = true, showLedger = true, modifierOnly = false,
	},
	scan = { fullScanOnOpen = false, chunkMs = 8, requestIntervalSec = 0.35, minFPS = 15, keepRawAuctions = false, historyDays = 30 },
	sniper = {
		enabled = false, intervalSec = 2.0, formula = "max(vendorsell, 35% dbmarket)", minProfit = "50s", sound = true,
		raidWarning = true, classRotation = true, ignoreOwn = true, maxPricePerDeal = "500g",
	},
	posting = {
		duration = 2, undercut = "1c", priceFormula = "max(postmin, min(dbminbuyout - undercut, dbmarket * 1.25))",
		minFormula = "max(vendorsell * 1.5, crafting * 1.05)", maxFormula = "max(dbmarket * 2.5, crafting * 3)",
		stackSizeCommodity = 0, keepQuantity = 0, ignoreSoulbound = true, skipIfBelowMin = true,
	},
	crafting = {
		restockTarget = 5, matFormula = "matprice", valueFormula = "max(dbminbuyout, dbmarket)", minProfit = "10s",
		minMarginPct = 10, includeVendorMats = true,
	},
	ledger = { trackVendor = true, trackMail = true, maxRows = 5000 },
	market = { halfLifeDays = 2, historicalHalfLifeDays = 14, ahCut = 0.05 },
	ui = { width = 900, height = 620, lastTab = "ledger" },
}

--------------------------------------------------------------------------------
-- Persistent root helpers (SPEC §2.1)
--------------------------------------------------------------------------------
local DB_VERSION = 1

local function newMeta()
	return { version = DB_VERSION, generation = 0, lastSavedAt = 0, lastSavedBy = "", createdAt = time(), build = FL.buildNumber }
end

local function newRoot()
	return { meta = newMeta(), settings = FL.DeepCopy(FL.DefaultSettings), tables = {} }
end

-- Fills keys missing from dst with (copies of) the defaults, recursively for nested tables.
local function mergeDefaults(dst, defaults)
	for k, v in pairs(defaults) do
		if type(v) == "table" then
			if type(dst[k]) ~= "table" then
				dst[k] = FL.DeepCopy(v)
			else
				mergeDefaults(dst[k], v)
			end
		elseif dst[k] == nil then
			dst[k] = v
		end
	end
	return dst
end

local function rootIsEmpty(root)
	if type(root) ~= "table" then return true end
	if type(root.meta) ~= "table" and type(root.settings) ~= "table" and type(root.tables) ~= "table" then return true end
	return false
end

local function rootGeneration(root)
	if type(root) == "table" and type(root.meta) == "table" then return tonumber(root.meta.generation) or 0 end
	return 0
end

-- Row count of an export blob { n = count, cols = { field = array } }.
local function blobRowCount(blob)
	if type(blob) ~= "table" then return 0 end
	local n = tonumber(blob.n)
	if n then return n end
	if type(blob.cols) == "table" then
		for _, col in pairs(blob.cols) do
			if type(col) == "table" then return #col end
		end
	end
	return 0
end

local function countAllRows(tables)
	local total = 0
	if type(tables) == "table" then
		for _, blob in pairs(tables) do total = total + blobRowCount(blob) end
	end
	return total
end

-- Builds a new blob keeping rows for which keep(cols, i) is true (all rows when keep is nil);
-- colList optionally restricts the columns copied.
local function filterBlob(blob, keep, colList)
	local out = { n = 0, cols = {} }
	if type(blob) ~= "table" or type(blob.cols) ~= "table" then return out end
	local src = blob.cols
	local names = colList
	if not names then
		names = {}
		for name in pairs(src) do names[#names + 1] = name end
		tsort(names)
	end
	local dst = out.cols
	local active, na = {}, 0
	for i = 1, #names do
		local name = names[i]
		if type(src[name]) == "table" then
			dst[name] = {}
			na = na + 1
			active[na] = name
		end
	end
	local n = blobRowCount(blob)
	local m = 0
	for i = 1, n do
		if keep == nil or keep(src, i) then
			m = m + 1
			for c = 1, na do
				local name = active[c]
				dst[name][m] = src[name][i]
			end
		end
	end
	out.n = m
	return out
end

local function keepCharRow(cols, i)
	return cols.charKey ~= nil and cols.charKey[i] == FL.playerKey
end

local function keepMarketRow(cols, i)
	return cols.marketKey == nil or cols.marketKey[i] == FL.marketKey
end

local COMPACT_MARKET_COLS = { "itemID", "suffix", "marketValue", "minBuyout", "lastScan" }
local EXPORT_MARKET_COLS = {
	"marketKey", "itemID", "suffix", "isCommodity", "marketValue", "minBuyout", "historical",
	"numAuctions", "soldPerDay", "numScans", "lastScan",
}

-- Per-character mirror: settings copy, this character's ledger rows, compact market rows of this market.
local function buildCharMirror(root)
	local tables = type(root.tables) == "table" and root.tables or {}
	return {
		meta = {
			version = DB_VERSION,
			generation = root.meta.generation,
			lastSavedAt = root.meta.lastSavedAt,
			playerKey = FL.playerKey,
			marketKey = FL.marketKey,
		},
		settings = root.settings,
		tables = {
			ledger = filterBlob(tables.ledger, keepCharRow),
			market = filterBlob(tables.market, keepMarketRow, COMPACT_MARKET_COLS),
		},
	}
end

local UNKNOWN_MARKET_KEY = "Unknown-Neutral"

-- Ensures a market blob carries marketKey / suffix / itemKeyStr columns for every row (compact
-- per-character blobs lack them); rows tagged with the placeholder market key are re-keyed.
local function normalizeMarketBlob(blob)
	if type(blob) ~= "table" or type(blob.cols) ~= "table" or type(blob.cols.itemID) ~= "table" then return blob end
	local cols = blob.cols
	local n = blobRowCount(blob)
	local itemIDs = cols.itemID
	local suffixes = cols.suffix or {}
	local marketKeys = cols.marketKey or {}
	local keys = cols.itemKeyStr or {}
	for i = 1, n do
		local itemID = tonumber(itemIDs[i]) or 0
		local suffix = tonumber(suffixes[i]) or 0
		local marketKey = marketKeys[i]
		local rekey = type(keys[i]) ~= "string"
		if type(marketKey) ~= "string" or (marketKey == UNKNOWN_MARKET_KEY and FL.marketKey ~= UNKNOWN_MARKET_KEY) then
			marketKey = FL.marketKey
			rekey = true
		end
		suffixes[i] = suffix
		marketKeys[i] = marketKey
		if rekey then keys[i] = marketKey .. ":" .. itemID .. ":" .. suffix end
	end
	cols.suffix = suffixes
	cols.marketKey = marketKeys
	cols.itemKeyStr = keys
	blob.n = n
	return blob
end

-- Dedupe key of a ledger row (ledger ids are per-database sequences and cannot be compared across files).
local function ledgerKey(ts, charKey, kind, itemID, quantity, total)
	return tostring(ts or 0) .. "|" .. tostring(charKey or "") .. "|" .. tostring(kind or "") .. "|"
		.. tostring(itemID or 0) .. "|" .. tostring(quantity or 0) .. "|" .. tostring(total or 0)
end

local function marketRowKey(cols, i)
	local marketKey = cols.marketKey and cols.marketKey[i]
	if type(marketKey) ~= "string" then marketKey = FL.marketKey end
	return marketKey .. ":" .. tostring((cols.itemID and cols.itemID[i]) or 0) .. ":" .. tostring((cols.suffix and cols.suffix[i]) or 0)
end

local function ledgerRowKey(cols, i)
	return ledgerKey(cols.ts and cols.ts[i], cols.charKey and cols.charKey[i], cols.kind and cols.kind[i],
		cols.itemID and cols.itemID[i], cols.quantity and cols.quantity[i], cols.total and cols.total[i])
end

-- Appends to base the rows of extra whose keyFn key is absent from base (base's columns only);
-- returns base and the index of the first appended row.
local function unionBlobs(base, extra, keyFn)
	if type(extra) ~= "table" or type(extra.cols) ~= "table" then return base, blobRowCount(base) + 1 end
	if type(base) ~= "table" or type(base.cols) ~= "table" then return FL.DeepCopy(extra), 1 end
	local bcols, ecols = base.cols, extra.cols
	local seen = {}
	local nb = blobRowCount(base)
	for i = 1, nb do seen[keyFn(bcols, i)] = true end
	local m = nb
	local ne = blobRowCount(extra)
	for i = 1, ne do
		local key = keyFn(ecols, i)
		if not seen[key] then
			seen[key] = true
			m = m + 1
			for name, col in pairs(bcols) do
				local srcCol = ecols[name]
				if type(srcCol) == "table" then
					col[m] = srcCol[i]
				else
					col[m] = nil
				end
			end
		end
	end
	base.n = m
	return base, nb + 1
end

-- Gives rows from fromIndex on fresh ids above every id used before them (keeps the unique index valid).
local function renumberLedgerIDs(blob, fromIndex)
	if type(blob) ~= "table" or type(blob.cols) ~= "table" or type(blob.cols.id) ~= "table" then return end
	local ids = blob.cols.id
	local n = blobRowCount(blob)
	local used, maxID = {}, 0
	for i = 1, fromIndex - 1 do
		local id = tonumber(ids[i])
		if id then
			used[id] = true
			if id > maxID then maxID = id end
		end
	end
	for i = fromIndex, n do
		local id = tonumber(ids[i])
		if not id or used[id] then
			maxID = maxID + 1
			id = maxID
		end
		used[id] = true
		if id > maxID then maxID = id end
		ids[i] = id
	end
end

--------------------------------------------------------------------------------
-- Hydration (ADDON_LOADED) and dehydration (PLAYER_LOGOUT / /fl save)
--------------------------------------------------------------------------------
-- Builds FL.RuntimeDB from the account / per-character SavedVariables (higher generation wins).
local function hydrate()
	local acct = _G.ForeverLedgerDB
	local char = _G.ForeverLedgerCharDB
	local acctEmpty, charEmpty = rootIsEmpty(acct), rootIsEmpty(char)
	local src, other, fromLabel
	if acctEmpty and charEmpty then
		FL.coldStartEmpty = true
		fromLabel = "defaults"
	elseif acctEmpty then
		src, fromLabel = char, "character"
	elseif charEmpty then
		src, fromLabel = acct, "account"
	elseif rootGeneration(char) > rootGeneration(acct) then
		src, other, fromLabel = char, acct, "character"
	else
		src, other, fromLabel = acct, char, "account"
	end
	local root = newRoot()
	if src then
		local copy = FL.DeepCopy(src)
		if type(copy.meta) == "table" then
			for k, v in pairs(copy.meta) do root.meta[k] = v end
		end
		if type(copy.settings) == "table" then
			root.settings = mergeDefaults(copy.settings, FL.DefaultSettings)
		end
		if type(copy.tables) == "table" then root.tables = copy.tables end
		if other and type(other.tables) == "table" then
			for name, blob in pairs(other.tables) do
				if root.tables[name] == nil then
					root.tables[name] = FL.DeepCopy(blob)
				elseif name == "market" then
					normalizeMarketBlob(root.tables.market)
					root.tables.market = normalizeMarketBlob((unionBlobs(root.tables.market, blob, marketRowKey)))
				elseif name == "ledger" then
					local merged, firstNew = unionBlobs(root.tables.ledger, blob, ledgerRowKey)
					renumberLedgerIDs(merged, firstNew)
					root.tables.ledger = merged
				end
			end
		end
	end
	root.meta.version = DB_VERSION
	root.meta.generation = (tonumber(root.meta.generation) or 0) + 1
	root.meta.build = FL.buildNumber
	root.meta.lastSavedAt = tonumber(root.meta.lastSavedAt) or 0
	if not tonumber(root.meta.createdAt) or tonumber(root.meta.createdAt) == 0 then root.meta.createdAt = time() end
	FL.RuntimeDB = root
	FL.Settings = root.settings
	FL.hydratedFrom = fromLabel
	local charSavedAt = 0
	if type(char) == "table" and type(char.meta) == "table" then charSavedAt = tonumber(char.meta.lastSavedAt) or 0 end
	FL.CharDB = {
		meta = { version = DB_VERSION, generation = root.meta.generation, lastSavedAt = charSavedAt, playerKey = FL.playerKey, marketKey = FL.marketKey },
		settings = root.settings,
		tables = {},
	}
	FL.hydrated = true
	FL:Debug("Hydrated from %s (generation %d, %d staged rows)", fromLabel, root.meta.generation, countAllRows(root.tables))
end

-- Pulls fresh export blobs from FL.Database (when loaded) into FL.RuntimeDB.tables and returns them.
local function liveBlobs()
	local root = FL.RuntimeDB
	if FL.Database and type(FL.Database.DehydrateAll) == "function" then
		local ok, blobs = pcall(FL.Database.DehydrateAll)
		if ok and type(blobs) == "table" then
			if root then
				for name, blob in pairs(blobs) do root.tables[name] = blob end
			end
			return root and root.tables or blobs
		elseif not ok then
			FL:Warn("DehydrateAll failed: %s", tostring(blobs))
		end
	end
	return root and root.tables or {}
end

-- Dehydrates FL.RuntimeDB into ForeverLedgerDB / ForeverLedgerCharDB (deep copies).
function FL.Persist()
	local root = FL.RuntimeDB
	if not root then return false end
	liveBlobs()
	root.meta.lastSavedAt = time()
	root.meta.lastSavedBy = FL.playerKey
	root.meta.build = FL.buildNumber
	root.meta.version = DB_VERSION
	local copy = FL.DeepCopy(root)
	_G.ForeverLedgerDB = copy
	local mirror = buildCharMirror(copy)
	_G.ForeverLedgerCharDB = mirror
	FL.CharDB = { meta = mirror.meta, settings = root.settings, tables = mirror.tables }
	local rows = countAllRows(copy.tables)
	FL:Print("Dehydrated %d rows to SavedVariables (generation %d). Clean logout.", rows, root.meta.generation)
	return true, rows
end

--------------------------------------------------------------------------------
-- Export / import strings
--------------------------------------------------------------------------------
-- Encodes settings, compact market rows and ledger rows into a user-visible string.
function FL.ExportString()
	local root = FL.RuntimeDB
	if not root then return nil, "database not hydrated yet" end
	local blobs = liveBlobs()
	local payload = {
		v = 1,
		exportedAt = time(),
		exportedBy = FL.playerKey,
		marketKey = FL.marketKey,
		settings = FL.DeepCopy(root.settings),
		market = filterBlob(blobs.market, nil, EXPORT_MARKET_COLS),
		ledger = filterBlob(blobs.ledger, nil),
	}
	return FL.Serializer.Encode(payload)
end

local importFields = {}

-- Merges imported market rows into the live market table; a row wins when its lastScan is newer.
local function importMarket(blob)
	local n = blobRowCount(blob)
	if n == 0 or type(blob.cols) ~= "table" or type(blob.cols.itemID) ~= "table" then return 0, 0 end
	local cols = blob.cols
	local db = FL.DB and FL.DB.market
	local updated, skipped = 0, 0
	if db and db.Upsert and db.FindFirst and db.Get then
		for i = 1, n do
			local itemID = tonumber(cols.itemID[i])
			if itemID then
				local marketKey = cols.marketKey and cols.marketKey[i]
				if type(marketKey) ~= "string" then marketKey = FL.marketKey end
				local suffix = tonumber(cols.suffix and cols.suffix[i]) or 0
				local key = marketKey .. ":" .. itemID .. ":" .. suffix
				local ts = tonumber(cols.lastScan and cols.lastScan[i]) or 0
				local rowID = db:FindFirst("itemKeyStr", key)
				local existingTs = -1
				if rowID then existingTs = tonumber(db:Get(rowID, "lastScan")) or 0 end
				if not rowID or ts > existingTs then
					wipe(importFields)
					for name, col in pairs(cols) do
						local v = col[i]
						if v ~= nil then importFields[name] = v end
					end
					importFields.marketKey = marketKey
					importFields.itemID = itemID
					importFields.suffix = suffix
					importFields.itemKeyStr = key
					local ok, err = pcall(db.Upsert, db, "itemKeyStr", key, importFields)
					if ok then
						updated = updated + 1
					else
						skipped = skipped + 1
						FL:Debug("Import market row %d rejected: %s", i, tostring(err))
					end
				else
					skipped = skipped + 1
				end
			else
				skipped = skipped + 1
			end
		end
	else
		local root = FL.RuntimeDB
		if root and blobRowCount(root.tables.market) < n then
			root.tables.market = FL.DeepCopy(blob)
			updated = n
		else
			skipped = n
		end
	end
	return updated, skipped
end

-- Appends imported ledger rows that do not already exist (same ts/char/kind/item/qty/total).
local function importLedger(blob)
	local n = blobRowCount(blob)
	if n == 0 or type(blob.cols) ~= "table" or type(blob.cols.ts) ~= "table" then return 0, 0 end
	local cols = blob.cols
	local db = FL.DB and FL.DB.ledger
	if db and db.Insert and db.ForEach and db.Get then
		local existing = {}
		local maxID = 0
		db:ForEach(function(rowID)
			existing[ledgerKey(db:Get(rowID, "ts"), db:Get(rowID, "charKey"), db:Get(rowID, "kind"),
				db:Get(rowID, "itemID"), db:Get(rowID, "quantity"), db:Get(rowID, "total"))] = true
			local id = tonumber(db:Get(rowID, "id")) or 0
			if id > maxID then maxID = id end
		end)
		local nextID = FL.Database and FL.Database.NextLedgerID
		local added, skipped = 0, 0
		for i = 1, n do
			local key = ledgerKey(cols.ts[i], cols.charKey and cols.charKey[i], cols.kind and cols.kind[i],
				cols.itemID and cols.itemID[i], cols.quantity and cols.quantity[i], cols.total and cols.total[i])
			if existing[key] then
				skipped = skipped + 1
			else
				existing[key] = true
				wipe(importFields)
				for name, col in pairs(cols) do
					local v = col[i]
					if v ~= nil then importFields[name] = v end
				end
				if type(nextID) == "function" then
					local ok, id = pcall(nextID)
					if ok and tonumber(id) then
						importFields.id = id
					else
						maxID = maxID + 1
						importFields.id = maxID
					end
				else
					maxID = maxID + 1
					importFields.id = maxID
				end
				local ok, err = pcall(db.Insert, db, importFields)
				if ok then
					added = added + 1
				else
					skipped = skipped + 1
					FL:Debug("Import ledger row %d rejected: %s", i, tostring(err))
				end
			end
		end
		return added, skipped
	end
	local root = FL.RuntimeDB
	if root and blobRowCount(root.tables.ledger) < n then
		root.tables.ledger = FL.DeepCopy(blob)
		return n, 0
	end
	return 0, n
end

-- Merges market/ledger rows from an export string (newest wins) and replaces settings; returns ok, err.
function FL.ImportString(str)
	if type(str) ~= "string" or strtrim(str) == "" then return false, "empty import string" end
	local data, err = FL.Serializer.Decode(str)
	if not data then return false, err end
	if tonumber(data.v) ~= 1 then return false, "unsupported export version " .. tostring(data.v) end
	local root = FL.RuntimeDB
	if not root then return false, "database not hydrated yet" end
	local marketUpdated, marketSkipped, ledgerAdded, ledgerSkipped = 0, 0, 0, 0
	if type(data.market) == "table" then marketUpdated, marketSkipped = importMarket(data.market) end
	if type(data.ledger) == "table" then ledgerAdded, ledgerSkipped = importLedger(data.ledger) end
	local settingsReplaced = false
	if type(data.settings) == "table" then
		local merged = mergeDefaults(FL.DeepCopy(data.settings), FL.DefaultSettings)
		wipe(root.settings)
		for k, v in pairs(merged) do root.settings[k] = v end
		settingsReplaced = true
	end
	if settingsReplaced then FL.Fire("FL_SETTINGS_CHANGED") end
	if marketUpdated > 0 then FL.Fire("FL_MARKET_UPDATED") end
	if ledgerAdded > 0 then FL.Fire("FL_LEDGER_CHANGED") end
	FL:Print("Import complete: %d market rows updated (%d skipped), %d ledger rows added (%d duplicates)%s.",
		marketUpdated, marketSkipped, ledgerAdded, ledgerSkipped, settingsReplaced and ", settings replaced" or "")
	return true
end

--------------------------------------------------------------------------------
-- FL.Secure — hardware-event dispatcher (SPEC §2.3)
--------------------------------------------------------------------------------
FL.Secure = { pending = {}, buttons = {} }
local SECURE_SLOTS = { "buy", "post", "cancel" }
local SECURE_NAMES = { buy = "ForeverLedgerSecureBuy", post = "ForeverLedgerSecurePost", cancel = "ForeverLedgerSecureCancel" }
local SECURE_DEFAULT_WIDTH, SECURE_DEFAULT_HEIGHT = 160, 24
local secureButtonsCreated = false

-- Runs the pending action of the clicked button synchronously inside the hardware click.
function FL.Secure.Dispatch(self, unit, button, actionType)
	local slot = self and self.flSlot
	if not slot then return end
	local action = FL.Secure.pending[slot]
	if not action then return end
	FL.Secure.pending[slot] = nil
	if not InCombatLockdown() then self:Hide() end
	local ok, err = pcall(action.fn, action, slot)
	if not ok then
		FL:Warn("Secure action '%s' failed: %s", tostring(action.label or slot), tostring(err))
		if type(action.onFail) == "function" then
			local okFail, failErr = pcall(action.onFail, err)
			if not okFail then reportHandlerError("Secure onFail", failErr) end
		end
	end
end

local function secureOnEnter(self)
	if not GameTooltip or not GameTooltip.SetOwner then return end
	local action = FL.Secure.pending[self.flSlot]
	GameTooltip:SetOwner(self, "ANCHOR_TOP")
	GameTooltip:AddLine(action and tostring(action.label or "") or "ForeverLedger", 1, 1, 1)
	GameTooltip:AddLine("Click to perform this auction action (hardware event).", 0.8, 0.8, 0.8, true)
	GameTooltip:Show()
end

local function secureOnLeave(self)
	if GameTooltip and GameTooltip.Hide then GameTooltip:Hide() end
end

-- Creates one secure button; standard template first, manual textures when the combo template fails.
local function createSecureButton(slot, name)
	local ok, btn = pcall(CreateFrame, "Button", name, UIParent, "SecureActionButtonTemplate, UIPanelButtonTemplate")
	if not ok or not btn then
		btn = CreateFrame("Button", name, UIParent, "SecureActionButtonTemplate")
		local normal = btn:CreateTexture(nil, "BACKGROUND")
		normal:SetTexture("Interface\\Buttons\\UI-Panel-Button-Up")
		normal:SetTexCoord(0, 0.625, 0, 0.6875)
		normal:SetAllPoints(btn)
		btn:SetNormalTexture(normal)
		local pushed = btn:CreateTexture(nil, "BACKGROUND")
		pushed:SetTexture("Interface\\Buttons\\UI-Panel-Button-Down")
		pushed:SetTexCoord(0, 0.625, 0, 0.6875)
		pushed:SetAllPoints(btn)
		btn:SetPushedTexture(pushed)
		local highlight = btn:CreateTexture(nil, "HIGHLIGHT")
		highlight:SetTexture("Interface\\Buttons\\UI-Panel-Button-Highlight")
		highlight:SetTexCoord(0, 0.625, 0, 0.6875)
		highlight:SetAllPoints(btn)
		highlight:SetBlendMode("ADD")
		btn:SetHighlightTexture(highlight)
		local label = btn:CreateFontString(nil, "OVERLAY", "GameFontNormal")
		label:SetPoint("CENTER", btn, "CENTER", 0, 0)
		btn:SetFontString(label)
	end
	btn:SetSize(SECURE_DEFAULT_WIDTH, SECURE_DEFAULT_HEIGHT)
	btn:SetPoint("CENTER", UIParent, "CENTER", 0, -220)
	btn:SetFrameStrata("DIALOG")
	btn.flSlot = slot
	btn.flLabel = btn:GetFontString()
	btn:RegisterForClicks("AnyUp", "AnyDown")
	btn:SetAttribute("type", "flaction")
	btn:SetAttribute("_flaction", FL.Secure.Dispatch)
	btn:SetAttribute("useOnKeyDown", false)
	btn:SetText("")
	btn:SetScript("OnEnter", secureOnEnter)
	btn:SetScript("OnLeave", secureOnLeave)
	btn:Hide()
	return btn
end

-- Creates the three secure buttons (out of combat only); idempotent.
local function createSecureButtons()
	if secureButtonsCreated then return true end
	if InCombatLockdown() then return false end
	for i = 1, #SECURE_SLOTS do
		local slot = SECURE_SLOTS[i]
		if not FL.Secure.buttons[slot] then
			local ok, btn = pcall(createSecureButton, slot, SECURE_NAMES[slot])
			if ok and btn then
				FL.Secure.buttons[slot] = btn
			else
				FL:Warn("Could not create secure button for '%s': %s", slot, tostring(btn))
			end
		end
	end
	secureButtonsCreated = FL.Secure.buttons.buy ~= nil and FL.Secure.buttons.post ~= nil and FL.Secure.buttons.cancel ~= nil
	return secureButtonsCreated
end

-- Returns the secure button frame for a slot ("buy" | "post" | "cancel").
function FL.Secure.GetButton(slot)
	return FL.Secure.buttons[slot]
end

-- Stores action = { label=, fn=, onFail= } for the slot, sets the label and shows the button; false in combat.
function FL.Secure.Arm(slot, action)
	if type(action) ~= "table" or type(action.fn) ~= "function" then return false end
	local btn = FL.Secure.buttons[slot]
	if not btn then
		if not createSecureButtons() then return false end
		btn = FL.Secure.buttons[slot]
		if not btn then return false end
	end
	if InCombatLockdown() then return false end
	FL.Secure.pending[slot] = action
	btn:SetText(tostring(action.label or "Click"))
	btn:Show()
	return true
end

-- Clears the pending action and hides the button (hide skipped while in combat).
function FL.Secure.Disarm(slot)
	FL.Secure.pending[slot] = nil
	local btn = FL.Secure.buttons[slot]
	if btn and not InCombatLockdown() then
		btn:Hide()
	end
	return true
end

-- True when the slot has a pending action.
function FL.Secure.IsArmed(slot)
	return FL.Secure.pending[slot] ~= nil
end

-- Re-parents and anchors the button to UI code's frame; out of combat only (returns false otherwise).
function FL.Secure.Attach(slot, parentFrame, point, relPoint, x, y, width, height)
	local btn = FL.Secure.buttons[slot]
	if not btn then return false end
	if InCombatLockdown() then return false end
	local parent = parentFrame or UIParent
	btn:SetParent(parent)
	btn:ClearAllPoints()
	btn:SetPoint(point or "CENTER", parent, relPoint or point or "CENTER", tonumber(x) or 0, tonumber(y) or 0)
	btn:SetSize(tonumber(width) or SECURE_DEFAULT_WIDTH, tonumber(height) or SECURE_DEFAULT_HEIGHT)
	if parent.GetFrameStrata and parent ~= UIParent then
		btn:SetFrameStrata(parent:GetFrameStrata())
		btn:SetFrameLevel((parent:GetFrameLevel() or 0) + 10)
	else
		btn:SetFrameStrata("DIALOG")
	end
	return true
end

--------------------------------------------------------------------------------
-- Slash commands (SPEC §2.4)
--------------------------------------------------------------------------------
local ACEGUI_HINT = "AceGUI-3.0 not found. Install the standalone Ace3 addon (CurseForge, flavour: WoW Forever) or copy Ace3/AceGUI-3.0, CallbackHandler-1.0 and LibStub into ForeverLedger/Libs/."

local HELP_LINES = {
	"/fl  or  /fl show — toggle the dashboard",
	"/fl scan — full Auction House scan (15-minute cooldown)",
	"/fl scan <itemID|itemLink> — scan a single item",
	"/fl snipe on|off — toggle the sniper (Auction House must be open)",
	"/fl post — build the posting queue from your bags",
	"/fl queue — build the crafting restock queue (top 10 shown)",
	"/fl price <formula> [itemID|itemLink] — evaluate a price formula",
	"/fl export — show the export string",
	"/fl import <string> — merge an export string",
	"/fl save — write the database to SavedVariables now",
	"/fl reset confirm — wipe the in-memory database to defaults",
	"/fl debug — toggle debug output",
	"/fl help — this list",
}

-- pcall wrapper for calls into other modules; prints the error and returns false on failure.
local function safeCall(fn, ...)
	local ok, a, b, c = pcall(fn, ...)
	if not ok then
		FL:Warn("Command failed: %s", tostring(a))
		return false
	end
	return true, a, b, c
end

-- Wipes the runtime database to defaults (keeps the settings table identity for cached references).
local function resetDatabase()
	local old = FL.RuntimeDB
	local root = newRoot()
	root.meta.generation = ((old and tonumber(old.meta.generation)) or 0) + 1
	if old and type(old.settings) == "table" then
		wipe(old.settings)
		for k, v in pairs(root.settings) do old.settings[k] = v end
		root.settings = old.settings
	end
	FL.RuntimeDB = root
	FL.Settings = root.settings
	FL.coldStartEmpty = false
	if FL.Database and type(FL.Database.tables) == "table" then
		for name, db in pairs(FL.Database.tables) do
			if type(db) == "table" and type(db.Truncate) == "function" then
				local ok, err = pcall(db.Truncate, db)
				if not ok then FL:Warn("Truncate of table %s failed: %s", tostring(name), tostring(err)) end
			end
		end
	end
	FL.CharDB = {
		meta = { version = DB_VERSION, generation = root.meta.generation, lastSavedAt = 0, playerKey = FL.playerKey, marketKey = FL.marketKey },
		settings = root.settings,
		tables = {},
	}
	FL.Fire("FL_SETTINGS_CHANGED")
	FL.Fire("FL_MARKET_UPDATED")
	FL.Fire("FL_LEDGER_CHANGED")
	return root.meta.generation
end

-- Prints the market summary of an item after a single-item scan.
local function reportItemScan(itemID)
	local name = FL.GetItemLinkCached(itemID) or FL.GetItemName(itemID) or ("item " .. tostring(itemID))
	local market = FL.Market
	if market and type(market.MarketValue) == "function" and type(market.MinBuyout) == "function"
		and type(market.NumAuctions) == "function" then
		local ok1, mv = pcall(market.MarketValue, itemID)
		local ok2, mb = pcall(market.MinBuyout, itemID)
		local ok3, na = pcall(market.NumAuctions, itemID)
		FL:Print("%s: market %s, min buyout %s, %d auction(s).", name,
			FL.FormatMoney(ok1 and mv or 0), FL.FormatMoney(ok2 and mb or 0), (ok3 and tonumber(na)) or 0)
	else
		FL:Print("Scan of %s finished.", name)
	end
end

-- Splits "<formula> [itemID|itemLink]" into formula text and an optional item id.
local function splitFormulaAndItem(rest)
	local hpos = strfind(rest, "|Hitem:", 1, true)
	if hpos then
		local cpos = strfind(rest, "|c", 1, true)
		local start = (cpos and cpos < hpos) and cpos or hpos
		return strtrim(strsub(rest, 1, start - 1)), FL.ItemIDFromLink(strsub(rest, start))
	end
	local head, tail = strmatch(rest, "^(.-)%s+(%d+)$")
	if head and tail and head ~= "" then return strtrim(head), tonumber(tail) end
	return rest, nil
end

-- Slash handler for /fl and /fledger.
function FL.Slash(msg)
	msg = strtrim(tostring(msg or ""))
	local cmd, rest = strmatch(msg, "^(%S*)%s*(.-)$")
	cmd = lower(cmd or "")
	rest = rest or ""
	if cmd == "" or cmd == "show" or cmd == "toggle" then
		if type(FL.ToggleDashboard) == "function" then
			safeCall(FL.ToggleDashboard)
		else
			FL:Print(ACEGUI_HINT)
		end
	elseif cmd == "scan" then
		local scanner = FL.AuctionScan
		if type(scanner) ~= "table" then
			FL:Warn("The auction scanner module is not loaded.")
			return
		end
		if not scanner.isOpen then
			FL:Warn("The Auction House is closed. Open it first, then use /fl scan.")
			return
		end
		if rest == "" then
			if type(scanner.RunFullScan) ~= "function" then
				FL:Warn("Full scan is unavailable.")
				return
			end
			local ok, started, reason = safeCall(scanner.RunFullScan, scanner)
			if ok and not started then FL:Warn("Full scan not started: %s", tostring(reason or "unknown reason")) end
		else
			local itemID = tonumber(rest) or FL.ItemIDFromLink(rest)
			if not itemID then
				FL:Warn("Usage: /fl scan <itemID|itemLink>")
				return
			end
			if type(scanner.ScanItem) == "function" then
				safeCall(scanner.ScanItem, scanner, itemID, reportItemScan)
			elseif type(scanner.RunCommodityScan) == "function" then
				safeCall(scanner.RunCommodityScan, scanner, itemID, reportItemScan)
			else
				FL:Warn("Single-item scans are unavailable.")
			end
		end
	elseif cmd == "snipe" then
		local sniper = FL.Sniper
		if type(sniper) ~= "table" or type(sniper.SetEnabled) ~= "function" then
			FL:Warn("The sniper module is not loaded.")
			return
		end
		local arg = lower(rest)
		local enable
		if arg == "on" or arg == "1" or arg == "true" then
			enable = true
		elseif arg == "off" or arg == "0" or arg == "false" then
			enable = false
		else
			enable = not (FL.Settings and FL.Settings.sniper and FL.Settings.sniper.enabled)
		end
		if safeCall(sniper.SetEnabled, sniper, enable) then
			FL:Print("Sniper %s%s.", enable and "enabled" or "disabled",
				(enable and FL.AuctionScan and not FL.AuctionScan.isOpen) and " (starts when the Auction House is open)" or "")
		end
	elseif cmd == "post" then
		local posting = FL.Posting
		if type(posting) ~= "table" or type(posting.BuildQueue) ~= "function" then
			FL:Warn("The posting module is not loaded.")
			return
		end
		local ok, queue = safeCall(posting.BuildQueue, posting)
		if ok then
			local n = (type(queue) == "table" and #queue) or 0
			FL:Print("Posting queue built: %d item(s). Open the dashboard Posting tab to price and post them.", n)
		end
	elseif cmd == "queue" then
		local crafting = FL.Crafting
		if type(crafting) ~= "table" or type(crafting.BuildQueue) ~= "function" then
			FL:Warn("The crafting module is not loaded.")
			return
		end
		local ok, queue = safeCall(crafting.BuildQueue, crafting)
		if ok and type(queue) == "table" then
			local n = #queue
			FL:Print("Crafting queue: %d entr%s.", n, (n == 1) and "y" or "ies")
			local shown = n
			if shown > 10 then shown = 10 end
			for i = 1, shown do
				local e = queue[i]
				if type(e) == "table" then
					local label = e.name or FL.GetItemName(e.itemID) or ("item " .. tostring(e.itemID))
					FL:Print("%d. %s x%d — cost %s, value %s, profit %s (%.0f%%), %.1f sold/day", i, tostring(label),
						tonumber(e.toCraft) or 0, FL.FormatMoney(e.cost or 0), FL.FormatMoney(e.value or 0),
						FL.FormatMoney(e.profit or 0), tonumber(e.marginPct) or 0, tonumber(e.soldPerDay) or 0)
				end
			end
		end
	elseif cmd == "price" then
		local parser = FL.Parser
		if type(parser) ~= "table" or type(parser.Evaluate) ~= "function" then
			FL:Warn("The formula parser module is not loaded.")
			return
		end
		local formula, itemID = splitFormulaAndItem(rest)
		if formula == "" then
			FL:Print("Usage: /fl price <formula> [itemID|itemLink]")
			return
		end
		local ok, value, err = safeCall(parser.Evaluate, formula, itemID, 0)
		if not ok then return end
		local target = ""
		if itemID then target = " for " .. (FL.GetItemLinkCached(itemID) or ("item " .. tostring(itemID))) end
		if value == nil then
			FL:Print("%s%s → no price (%s).", formula, target, tostring(err or "a price source is unavailable"))
		else
			FL:Print("%s%s = %s (%s copper)", formula, target, FL.FormatMoney(value), tostring(FL.Round(value)))
		end
	elseif cmd == "export" then
		if type(FL.ShowExportFrame) == "function" then
			safeCall(FL.ShowExportFrame)
		else
			local s, err = FL.ExportString()
			if not s then
				FL:Warn("Export failed: %s", tostring(err))
				return
			end
			FL:Print("Export string (%d characters; first 200 shown):", strlen(s))
			chatMessage(strsub(s, 1, 200))
			FL:Print("Install AceGUI-3.0 (see /fl show) to copy the full string from a text box. Keep exports safe: /fl import <string> restores them after a failed cold start.")
		end
	elseif cmd == "import" then
		if rest == "" then
			FL:Print("Usage: /fl import <export string>")
			return
		end
		local ok, err = FL.ImportString(rest)
		if not ok then FL:Warn("Import failed: %s", tostring(err)) end
	elseif cmd == "save" then
		if not FL.Persist() then FL:Warn("Nothing to save yet: the database is not hydrated.") end
	elseif cmd == "reset" then
		if lower(rest) == "confirm" then
			local generation = resetDatabase()
			FL:Print("Database reset to defaults in memory (generation %d). It is written at logout, /reload or /fl save.", generation)
		else
			FL:Print("This wipes ALL ForeverLedger data in memory. Type |cffffff00/fl reset confirm|r to proceed (run /fl export first if unsure).")
		end
	elseif cmd == "debug" then
		if not FL.Settings then
			FL:Warn("Settings are not loaded yet.")
			return
		end
		FL.Settings.debug = not FL.Settings.debug
		FL:Print("Debug output %s.", FL.Settings.debug and "ON" or "OFF")
		FL.Fire("FL_SETTINGS_CHANGED")
	elseif cmd == "help" then
		FL:Print("ForeverLedger v%s commands:", FL.version)
		for i = 1, #HELP_LINES do chatMessage("  " .. HELP_LINES[i]) end
	else
		FL:Warn("Unknown command '%s'. Type /fl help for the list.", cmd)
	end
end

SLASH_FOREVERLEDGER1 = "/fledger"
SLASH_FOREVERLEDGER2 = "/fl"
SlashCmdList["FOREVERLEDGER"] = function(msg)
	FL.Slash(msg)
end

--------------------------------------------------------------------------------
-- Lifecycle: ADDON_LOADED → hydrate; PLAYER_LOGIN → FL_DB_READY + banner; PLAYER_LOGOUT → Persist
--------------------------------------------------------------------------------
-- Live row count of a Database table when loaded, else nil.
local function liveCount(name)
	local db = FL.DB and FL.DB[name]
	if type(db) == "table" and type(db.Count) == "function" then
		local ok, n = pcall(db.Count, db)
		if ok and tonumber(n) then return tonumber(n) end
	end
	return nil
end

-- Prints the cold-start safeguard banner and the empty-database warnings (SPEC §2.1 step 5).
local function printBanner()
	local root = FL.RuntimeDB
	local marketRows = liveCount("market") or blobRowCount(root.tables.market)
	local ledgerRows = liveCount("ledger") or blobRowCount(root.tables.ledger)
	local lastSaved = tonumber(root.meta.lastSavedAt) or 0
	local when = "never"
	if lastSaved > 0 then when = tostring(date("%Y-%m-%d %H:%M", lastSaved)) end
	chatMessage(format("ForeverLedger v%s: WoW Forever cold-start safeguard ACTIVE — %d market rows, %d ledger rows hydrated into memory (generation %d, last saved %s).",
		FL.version, marketRows, ledgerRows, tonumber(root.meta.generation) or 0, when))
	if FL.coldStartEmpty then
		if FL.buildNumber < 70009 then
			FL:Warn("Your database is EMPTY on a cold start. This Forever build (%d) is known to skip loading SavedVariables. Use /fl import to restore from an export string; use /fl export regularly.", FL.buildNumber)
		end
		FL:Warn("No saved data found — if you expected data, type /fl import before logging out, or the empty database will overwrite your saved file at logout.")
	end
end

local function onRegenEnabled(event)
	if createSecureButtons() then FL.UnregisterEvent("PLAYER_REGEN_ENABLED", onRegenEnabled) end
end

local function onAddonLoaded(event, name)
	if name ~= addonName then return end
	FL.UnregisterEvent("ADDON_LOADED", onAddonLoaded)
	resolveIdentity()
	hydrate()
	if not createSecureButtons() then FL.RegisterEvent("PLAYER_REGEN_ENABLED", onRegenEnabled) end
end

local function onPlayerLogin(event)
	resolveIdentity()
	if not FL.hydrated then hydrate() end
	if not secureButtonsCreated and not createSecureButtons() then
		FL.RegisterEvent("PLAYER_REGEN_ENABLED", onRegenEnabled)
	end
	local root = FL.RuntimeDB
	if FL.CharDB and type(FL.CharDB.meta) == "table" then
		FL.CharDB.meta.playerKey = FL.playerKey
		FL.CharDB.meta.marketKey = FL.marketKey
	end
	if type(root.tables) ~= "table" then root.tables = {} end
	if type(root.tables.market) == "table" then normalizeMarketBlob(root.tables.market) end
	if FL.Database and type(FL.Database.HydrateAll) == "function" then
		local ok, err = pcall(FL.Database.HydrateAll, root.tables)
		if not ok then FL:Warn("Database hydration failed: %s", tostring(err)) end
	end
	FL.dbReady = true
	FL.Fire("FL_DB_READY")
	printBanner()
end

local function onPlayerLogout(event)
	FL.Persist()
end

FL.RegisterEvent("ADDON_LOADED", onAddonLoaded)
FL.RegisterEvent("PLAYER_LOGIN", onPlayerLogin)
FL.RegisterEvent("PLAYER_LOGOUT", onPlayerLogout)
