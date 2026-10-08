local addonName, FL = ...

--------------------------------------------------------------------------------
-- Database.lua
-- ForeverLedger relational in-memory database: schema-typed, column-oriented
-- (struct-of-arrays) tables with hash indexes, a fluent row builder, a pooled
-- query builder with allocation-free iteration, the table definitions used by
-- every other file (FL.DB) and the FL.Market helpers that operate on the
-- market table.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Cached globals
--------------------------------------------------------------------------------
local pairs, type, tonumber, tostring = pairs, type, tonumber, tostring
local setmetatable, error = setmetatable, error
local format, strlower, strfind = string.format, string.lower, string.find
local tsort = table.sort
local floor, huge = math.floor, math.huge
local time = time
local C_Timer = C_Timer
local wipe = wipe
if not wipe then
	wipe = function(t)
		for k in pairs(t) do
			t[k] = nil
		end
		return t
	end
end

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------
local DAY_SEC = 86400
local DEFAULT_HALF_LIFE_DAYS = 2          -- settings.market.halfLifeDays fallback
local DEFAULT_HIST_HALF_LIFE_DAYS = 14    -- settings.market.historicalHalfLifeDays fallback
local DEFAULT_HISTORY_DAYS = 30           -- settings.scan.historyDays fallback
local SALE_WINDOW_SEC = 7200              -- sale estimates only between sightings closer than 2h
local HISTORY_BUCKET_SEC = 6 * 3600       -- scans closer than this update the latest history row in place
local HISTORY_MAX_ROWS = 150000           -- hard cap on history rows (retention is halved until under cap)
local HISTORY_SWEEP_INTERVAL = 3600       -- global history prune at most once per hour
local MARKET_SIGNAL_DELAY = 0.25          -- coalescing delay for FL_MARKET_UPDATED
local QUERY_POOL_MAX = 32                 -- pooled query contexts per table
local INDEX_ARRAY_POOL_MAX = 512          -- pooled index arrays (shared by all tables)
local MIN_FIRST_SCANS = 5                 -- EMA warm-up: first scans use a plain running average

--------------------------------------------------------------------------------
-- Shared helpers
--------------------------------------------------------------------------------
local function round(x)
	return floor(x + 0.5)
end

-- tonumber() that also rejects NaN; returns fallback when the value is unusable.
local function sanitizeNumber(v, fallback)
	v = tonumber(v)
	if v == nil or v ~= v then
		return fallback
	end
	return v
end

-- FL.marketKey, or realm-faction assembled from Core's keys before PLAYER_LOGIN.
local function currentMarketKey()
	local mk = FL.marketKey
	if type(mk) ~= "string" or mk == "" then
		mk = tostring(FL.realmKey or "Unknown") .. "-" .. tostring(FL.factionKey or "Neutral")
	end
	return mk
end

--------------------------------------------------------------------------------
-- Namespace, prototypes and metatables
--------------------------------------------------------------------------------
local Database = { tables = {} }
FL.Database = Database

local DBProto = {}
local DBMeta = { __index = DBProto }

local Builder = {}
local BuilderMeta = { __index = Builder }

local Query = {}
local QueryMeta = { __index = Query }

local EMPTY_FIELDS = {}
local VALID_TYPES = { string = true, number = true, boolean = true }
local TYPE_RANK = { ["nil"] = 0, boolean = 1, number = 2, string = 3 }

-- Query condition operators
local OP_EQ, OP_NE, OP_GT, OP_GE, OP_LT, OP_LE, OP_CONTAINS, OP_CUSTOM = 1, 2, 3, 4, 5, 6, 7, 8

--------------------------------------------------------------------------------
-- Error and type-check helpers
--------------------------------------------------------------------------------
local function describeValue(value)
	if value == nil then
		return "nil"
	end
	local t = type(value)
	if t == "number" and value ~= value then
		return "NaN"
	end
	return t
end

local function fieldError(db, field, want, got, level)
	error(format("ForeverLedger.Database[%s]: field '%s' expects %s, got %s", db.name, tostring(field), want, got), level or 2)
end

local function dbError(db, msg, level)
	error(format("ForeverLedger.Database[%s]: %s", db.name, msg), level or 2)
end

-- Type-checks a value for a field definition and returns the value to store
-- (the default is applied for nil). `level` is the error level blaming the API caller.
local function coerceValue(db, field, def, value, level)
	if value == nil then
		if def.default ~= nil then
			return def.default
		end
		if def.nilable then
			return nil
		end
		fieldError(db, field, def.type, "nil", level)
	end
	local t = type(value)
	if t ~= def.type or (t == "number" and value ~= value) then
		fieldError(db, field, def.type, describeValue(value), level)
	end
	return value
end

--------------------------------------------------------------------------------
-- Index maintenance (unique: map[value] = rowID ; index: map[value] = { rowIDs })
--------------------------------------------------------------------------------
local indexArrayPool = {}
local indexArrayPoolN = 0

local function acquireIndexArray()
	if indexArrayPoolN > 0 then
		local arr = indexArrayPool[indexArrayPoolN]
		indexArrayPool[indexArrayPoolN] = nil
		indexArrayPoolN = indexArrayPoolN - 1
		return arr
	end
	return {}
end

local function releaseIndexArray(arr)
	if indexArrayPoolN < INDEX_ARRAY_POOL_MAX then
		indexArrayPoolN = indexArrayPoolN + 1
		indexArrayPool[indexArrayPoolN] = arr
	end
end

local function indexAdd(db, field, value, rowID)
	if value == nil then
		return
	end
	local umap = db.uniques[field]
	if umap then
		umap[value] = rowID
		return
	end
	local map = db.indexes[field]
	local arr = map[value]
	if not arr then
		arr = acquireIndexArray()
		map[value] = arr
	end
	arr[#arr + 1] = rowID
end

local function indexRemove(db, field, value, rowID)
	if value == nil then
		return
	end
	local umap = db.uniques[field]
	if umap then
		if umap[value] == rowID then
			umap[value] = nil
		end
		return
	end
	local map = db.indexes[field]
	local arr = map[value]
	if not arr then
		return
	end
	local n = #arr
	for i = 1, n do
		if arr[i] == rowID then
			arr[i] = arr[n]
			arr[n] = nil
			break
		end
	end
	if arr[1] == nil then
		map[value] = nil
		releaseIndexArray(arr)
	end
end

local function indexReplace(db, field, value, oldRowID, newRowID)
	if value == nil then
		return
	end
	local umap = db.uniques[field]
	if umap then
		umap[value] = newRowID
		return
	end
	local arr = db.indexes[field][value]
	if not arr then
		return
	end
	for i = 1, #arr do
		if arr[i] == oldRowID then
			arr[i] = newRowID
			return
		end
	end
end

local function resetIndexes(db)
	for _, map in pairs(db.uniques) do
		wipe(map)
	end
	for _, map in pairs(db.indexes) do
		for _, arr in pairs(map) do
			wipe(arr)
			releaseIndexArray(arr)
		end
		wipe(map)
	end
end

--------------------------------------------------------------------------------
-- Schema compilation
--------------------------------------------------------------------------------
local function compileSchema(db, schema)
	if type(schema) ~= "table" or type(schema.fields) ~= "table" then
		dbError(db, "schema.fields table required", 4)
	end
	local defs, names = {}, {}
	for fname, raw in pairs(schema.fields) do
		if type(fname) ~= "string" or fname == "" then
			dbError(db, "field names must be non-empty strings", 4)
		end
		if type(raw) ~= "table" or not VALID_TYPES[raw.type] then
			dbError(db, format("field '%s' has an invalid type (%s)", fname, tostring(type(raw) == "table" and raw.type or raw)), 4)
		end
		local def = {
			type = raw.type,
			default = raw.default,
			index = raw.index and true or false,
			unique = raw.unique and true or false,
			nilable = raw.nilable and true or false,
		}
		if def.default ~= nil and type(def.default) ~= def.type then
			dbError(db, format("field '%s' default does not match type %s", fname, def.type), 4)
		end
		defs[fname] = def
		names[#names + 1] = fname
	end
	tsort(names)
	local list, seen = {}, {}
	if type(schema.order) == "table" then
		for i = 1, #schema.order do
			local fname = schema.order[i]
			if defs[fname] and not seen[fname] then
				seen[fname] = true
				list[#list + 1] = fname
			end
		end
	end
	for i = 1, #names do
		local fname = names[i]
		if not seen[fname] then
			seen[fname] = true
			list[#list + 1] = fname
		end
	end
	local indexed = {}
	for i = 1, #list do
		local fname = list[i]
		local def = defs[fname]
		if def.unique then
			db.uniques[fname] = {}
			indexed[#indexed + 1] = fname
		elseif def.index then
			db.indexes[fname] = {}
			indexed[#indexed + 1] = fname
		end
		db.cols[fname] = {}
	end
	db.fields = defs
	db.fieldList = list
	db.nFields = #list
	db.indexedList = indexed
	-- optional file-local hook: derive(row) fills derived fields that an older/compact blob lacks
	if type(schema.derive) == "function" then
		db.derive = schema.derive
	else
		db.derive = nil
	end
end

--------------------------------------------------------------------------------
-- Row staging (validate everything before touching the columns)
--------------------------------------------------------------------------------
-- Validates a full row from `fields` into db.scratch: defaults applied, unique
-- values checked against the live indexes. `keyField`/`keyValue` override one field.
local function stageRow(db, fields, level, keyField, keyValue)
	local defs = db.fields
	for k in pairs(fields) do
		if not defs[k] then
			dbError(db, format("unknown field '%s'", tostring(k)), level)
		end
	end
	local scratch, list, uniques = db.scratch, db.fieldList, db.uniques
	for i = 1, db.nFields do
		local f = list[i]
		local raw = fields[f]
		if f == keyField then
			raw = keyValue
		end
		local v = coerceValue(db, f, defs[f], raw, level + 1)
		local umap = uniques[f]
		if umap and v ~= nil and umap[v] ~= nil then
			dbError(db, format("duplicate value %s for unique field '%s'", tostring(v), f), level)
		end
		scratch[f] = v
	end
	return scratch
end

-- Appends the staged row as a new row and maintains the indexes.
local function commitRow(db, staged)
	local rowID = db.n + 1
	local list, cols = db.fieldList, db.cols
	for i = 1, db.nFields do
		local f = list[i]
		cols[f][rowID] = staged[f]
	end
	local indexed = db.indexedList
	for i = 1, #indexed do
		local f = indexed[i]
		indexAdd(db, f, staged[f], rowID)
	end
	db.n = rowID
	return rowID
end

--------------------------------------------------------------------------------
-- FL.Database:New — table construction and registry
--------------------------------------------------------------------------------
--- Creates and registers a table: FL.Database:New(tableName, schema) -> db.
function Database.New(self, tableName, schema)
	if type(self) == "string" then
		self, tableName, schema = Database, self, tableName
	end
	if type(tableName) ~= "string" or tableName == "" then
		error("ForeverLedger.Database: table name must be a non-empty string", 2)
	end
	local db = setmetatable({
		name = tableName,
		schema = schema,
		persistent = (type(schema) == "table" and schema.persistent ~= false) and true or false,
		cols = {},
		n = 0,
		indexes = {},
		uniques = {},
		version = 0,
		queryPool = {},
		queryPoolN = 0,
		builderPool = {},
		scratch = {},
	}, DBMeta)
	compileSchema(db, schema)
	db.exportBlob = { n = 0, cols = db.cols }
	db.cursorMeta = {
		__index = function(cursor, field)
			return db:Get(cursor.rowID, field)
		end,
	}
	Database.tables[tableName] = db
	return db
end

--- Returns the registered table instance for a name (or nil).
function Database.Get(tableName)
	return Database.tables[tableName]
end

--------------------------------------------------------------------------------
-- Row builder
--------------------------------------------------------------------------------
--- Sets one field on the pending row (type-checked immediately); chainable.
function Builder:SetField(field, value)
	local db = self.db
	if self.released then
		dbError(db, "row builder used after Create()", 3)
	end
	local def = db.fields[field]
	if not def then
		dbError(db, format("unknown field '%s'", tostring(field)), 3)
	end
	if value ~= nil then
		coerceValue(db, field, def, value, 4)
	end
	self.values[field] = value
	return self
end

--- Inserts the pending row (defaults applied, unique indexes enforced) and returns its rowID.
function Builder:Create()
	local db = self.db
	if self.released then
		dbError(db, "row builder used after Create()", 3)
	end
	local staged = stageRow(db, self.values, 4)
	local rowID = commitRow(db, staged)
	self.released = true
	wipe(self.values)
	local pool = db.builderPool
	pool[#pool + 1] = self
	return rowID
end

--- Returns a (pooled) fluent row builder for this table.
function DBProto:NewRow()
	local pool = self.builderPool
	local n = #pool
	local builder
	if n > 0 then
		builder = pool[n]
		pool[n] = nil
		builder.released = false
	else
		builder = setmetatable({ db = self, values = {}, released = false }, BuilderMeta)
	end
	return builder
end

--------------------------------------------------------------------------------
-- Row CRUD
--------------------------------------------------------------------------------
--- Inserts a row from a fields table; returns the new rowID.
function DBProto:Insert(fields)
	if type(fields) ~= "table" then
		dbError(self, "Insert expects a table of fields", 3)
	end
	local staged = stageRow(self, fields, 4)
	return commitRow(self, staged)
end

--- Returns the number of live rows.
function DBProto:Count()
	return self.n
end

--- Returns the value of `field` for `rowID` (nil when the rowID is out of range).
function DBProto:Get(rowID, field)
	local col = self.cols[field]
	if not col then
		dbError(self, format("unknown field '%s'", tostring(field)), 3)
	end
	if type(rowID) ~= "number" or rowID < 1 or rowID > self.n then
		return nil
	end
	return col[rowID]
end

--- Sets `field` on `rowID` (type-checked; indexes maintained; unique conflicts error).
function DBProto:Set(rowID, field, value)
	local def = self.fields[field]
	if not def then
		dbError(self, format("unknown field '%s'", tostring(field)), 3)
	end
	if type(rowID) ~= "number" or rowID < 1 or rowID > self.n then
		dbError(self, format("invalid rowID %s", tostring(rowID)), 3)
	end
	value = coerceValue(self, field, def, value, 4)
	local col = self.cols[field]
	local old = col[rowID]
	if old == value then
		return
	end
	if def.unique then
		if value ~= nil then
			local existing = self.uniques[field][value]
			if existing ~= nil and existing ~= rowID then
				dbError(self, format("duplicate value %s for unique field '%s'", tostring(value), field), 3)
			end
		end
		indexRemove(self, field, old, rowID)
		col[rowID] = value
		indexAdd(self, field, value, rowID)
	elseif def.index then
		indexRemove(self, field, old, rowID)
		col[rowID] = value
		indexAdd(self, field, value, rowID)
	else
		col[rowID] = value
	end
end

--- Sets several fields on `rowID`; everything is validated before anything is written.
function DBProto:SetMany(rowID, fields)
	if type(fields) ~= "table" then
		dbError(self, "SetMany expects a table of fields", 3)
	end
	if type(rowID) ~= "number" or rowID < 1 or rowID > self.n then
		dbError(self, format("invalid rowID %s", tostring(rowID)), 3)
	end
	local defs, uniques = self.fields, self.uniques
	for k, v in pairs(fields) do
		local def = defs[k]
		if not def then
			dbError(self, format("unknown field '%s'", tostring(k)), 3)
		end
		local nv = coerceValue(self, k, def, v, 4)
		local umap = uniques[k]
		if umap and nv ~= nil then
			local existing = umap[nv]
			if existing ~= nil and existing ~= rowID then
				dbError(self, format("duplicate value %s for unique field '%s'", tostring(nv), k), 3)
			end
		end
	end
	for k, v in pairs(fields) do
		self:Set(rowID, k, v)
	end
end

--- Deletes a row by swapping the last row into its slot; returns the moved row's old rowID (or nil).
function DBProto:Delete(rowID)
	local n = self.n
	if type(rowID) ~= "number" or rowID < 1 or rowID > n then
		return nil
	end
	local cols, list, nFields = self.cols, self.fieldList, self.nFields
	local indexed = self.indexedList
	local nIndexed = #indexed
	for i = 1, nIndexed do
		local f = indexed[i]
		indexRemove(self, f, cols[f][rowID], rowID)
	end
	local moved = nil
	if rowID ~= n then
		for i = 1, nIndexed do
			local f = indexed[i]
			indexReplace(self, f, cols[f][n], n, rowID)
		end
		for i = 1, nFields do
			local col = cols[list[i]]
			col[rowID] = col[n]
			col[n] = nil
		end
		moved = n
	else
		for i = 1, nFields do
			cols[list[i]][n] = nil
		end
	end
	self.n = n - 1
	return moved
end

--- Removes every row (columns and indexes are emptied, capacity is kept).
function DBProto:Truncate()
	local cols, list = self.cols, self.fieldList
	for i = 1, self.nFields do
		wipe(cols[list[i]])
	end
	resetIndexes(self)
	self.n = 0
	self.version = self.version + 1
end

--------------------------------------------------------------------------------
-- Lookups
--------------------------------------------------------------------------------
--- Returns the first rowID whose `field` equals `value` (O(1) when indexed), or nil.
function DBProto:FindFirst(field, value)
	local def = self.fields[field]
	if not def then
		dbError(self, format("unknown field '%s'", tostring(field)), 3)
	end
	local col = self.cols[field]
	if value == nil then
		for i = 1, self.n do
			if col[i] == nil then
				return i
			end
		end
		return nil
	end
	local umap = self.uniques[field]
	if umap then
		return umap[value]
	end
	local map = self.indexes[field]
	if map then
		local arr = map[value]
		return arr and arr[1] or nil
	end
	for i = 1, self.n do
		if col[i] == value then
			return i
		end
	end
	return nil
end

--- Fills `outArray` (wiped first) with every rowID whose `field` equals `value`; sets outArray.n.
function DBProto:FindAll(field, value, outArray)
	local def = self.fields[field]
	if not def then
		dbError(self, format("unknown field '%s'", tostring(field)), 3)
	end
	local out = outArray or {}
	local prev = out.n or #out
	for i = 1, prev do
		out[i] = nil
	end
	local count = 0
	local col = self.cols[field]
	if value == nil then
		for i = 1, self.n do
			if col[i] == nil then
				count = count + 1
				out[count] = i
			end
		end
	else
		local umap = self.uniques[field]
		local map = (not umap) and self.indexes[field] or nil
		if umap then
			local rowID = umap[value]
			if rowID then
				count = 1
				out[1] = rowID
			end
		elseif map then
			local arr = map[value]
			if arr then
				count = #arr
				for i = 1, count do
					out[i] = arr[i]
				end
			end
		else
			for i = 1, self.n do
				if col[i] == value then
					count = count + 1
					out[count] = i
				end
			end
		end
	end
	out.n = count
	return out
end

--- Updates the row whose unique `keyField` equals `keyValue`, or inserts it; returns rowID, created.
function DBProto:Upsert(keyField, keyValue, fields)
	local umap = self.uniques[keyField]
	if not umap then
		dbError(self, format("Upsert requires a unique-indexed key field, got '%s'", tostring(keyField)), 3)
	end
	if keyValue == nil then
		dbError(self, format("Upsert key value for '%s' must not be nil", keyField), 3)
	end
	if fields ~= nil and type(fields) ~= "table" then
		dbError(self, "Upsert expects a table of fields", 3)
	end
	local rowID = umap[keyValue]
	if rowID then
		if fields then
			local given = fields[keyField]
			if given ~= nil and given ~= keyValue then
				dbError(self, format("Upsert fields change the key '%s' (%s -> %s)", keyField, tostring(keyValue), tostring(given)), 3)
			end
			self:SetMany(rowID, fields)
		end
		return rowID, false
	end
	local staged = stageRow(self, fields or EMPTY_FIELDS, 4, keyField, keyValue)
	return commitRow(self, staged), true
end

--- Calls fn(rowID) for rows 1..n; stops early when fn returns true.
function DBProto:ForEach(fn)
	for rowID = 1, self.n do
		if fn(rowID) then
			return
		end
	end
end

--------------------------------------------------------------------------------
-- Export / Import (persistence blobs)
--------------------------------------------------------------------------------
--- Returns { n = count, cols = { field = array } }; the arrays are direct references to the live columns.
function DBProto:Export()
	local blob = self.exportBlob
	blob.n = self.n
	return blob
end

-- Converts a stored value to the field type when possible (nil when it cannot be used).
local function importValue(def, v)
	local want = def.type
	local t = type(v)
	if t ~= want then
		if want == "number" then
			v = tonumber(v)
		elseif want == "string" then
			if t == "number" then
				v = tostring(v)
			else
				v = nil
			end
		elseif want == "boolean" then
			if v == 1 or v == "true" then
				v = true
			elseif v == 0 or v == "false" then
				v = false
			else
				v = nil
			end
		else
			v = nil
		end
	end
	if type(v) == "number" and v ~= v then
		v = nil
	end
	return v
end

--- Replaces the contents from a blob; missing columns get defaults, extra columns are ignored,
--- invalid rows are skipped and the indexes are rebuilt. Returns rowsImported, rowsSkipped.
function DBProto:Import(blob)
	local srcCols = nil
	local n = 0
	if type(blob) == "table" then
		if type(blob.cols) == "table" then
			srcCols = blob.cols
		end
		n = tonumber(blob.n) or 0
	end
	local list, defs, nFields = self.fieldList, self.fields, self.nFields
	if srcCols and n <= 0 then
		for i = 1, nFields do
			local arr = srcCols[list[i]]
			if type(arr) == "table" then
				local len = #arr
				if len > n then
					n = len
				end
			end
		end
	end
	local newCols = {}
	for i = 1, nFields do
		newCols[list[i]] = {}
	end
	resetIndexes(self)
	local scratch, uniques, indexed = self.scratch, self.uniques, self.indexedList
	local derive = self.derive
	local nIndexed = #indexed
	local count, skipped = 0, 0
	for r = 1, n do
		local ok = true
		-- pass 1: raw values (type-coerced, nil when missing/unusable)
		for i = 1, nFields do
			local f = list[i]
			local src = srcCols and srcCols[f]
			local v = nil
			if type(src) == "table" then
				v = src[r]
			end
			if v ~= nil then
				v = importValue(defs[f], v)
			end
			scratch[f] = v
		end
		if derive then
			derive(scratch)
		end
		-- pass 2: defaults, required fields, unique constraints
		for i = 1, nFields do
			local f = list[i]
			local def = defs[f]
			local v = scratch[f]
			if v ~= nil and type(v) ~= def.type then
				v = importValue(def, v)
				scratch[f] = v
			end
			if v == nil then
				if def.default ~= nil then
					v = def.default
					scratch[f] = v
				elseif not def.nilable then
					ok = false
					break
				end
			end
			if v ~= nil then
				local umap = uniques[f]
				if umap and umap[v] ~= nil then
					ok = false
					break
				end
			end
		end
		if ok then
			count = count + 1
			for i = 1, nFields do
				local f = list[i]
				newCols[f][count] = scratch[f]
			end
			for i = 1, nIndexed do
				local f = indexed[i]
				indexAdd(self, f, scratch[f], count)
			end
		else
			skipped = skipped + 1
		end
	end
	local cols = self.cols
	for i = 1, nFields do
		local f = list[i]
		cols[f] = newCols[f]
	end
	self.n = count
	self.version = self.version + 1
	if skipped > 0 and FL.Warn then
		FL:Warn("Database[%s]: skipped %d invalid row(s) while importing %d row(s).", self.name, skipped, n)
	end
	return count, skipped
end

--------------------------------------------------------------------------------
-- Query builder (pooled contexts, allocation-free iteration)
--------------------------------------------------------------------------------
-- Three-way comparison usable for mixed/nil column values (never errors).
local function compareValues(va, vb)
	if va == vb then
		return 0
	end
	local ta, tb = type(va), type(vb)
	if ta ~= tb then
		if (TYPE_RANK[ta] or 0) < (TYPE_RANK[tb] or 0) then
			return -1
		end
		return 1
	end
	if ta == "number" or ta == "string" then
		if va < vb then
			return -1
		end
		return 1
	end
	if ta == "boolean" then
		if va == false then
			return -1
		end
		return 1
	end
	return 0
end

-- Evaluates one non-custom condition against a row.
local function condMatches(cond, rowID)
	local op = cond.op
	local v = cond.col[rowID]
	local want = cond.value
	if op == OP_EQ then
		return v == want
	elseif op == OP_NE then
		return v ~= want
	elseif op == OP_CONTAINS then
		if type(v) ~= "string" then
			return false
		end
		return strfind(strlower(v), want, 1, true) ~= nil
	end
	local tv = type(v)
	if tv ~= type(want) or (tv ~= "number" and tv ~= "string") then
		return false
	end
	if op == OP_GT then
		return v > want
	elseif op == OP_GE then
		return v >= want
	elseif op == OP_LT then
		return v < want
	end
	return v <= want
end

-- Evaluates every condition except the one already satisfied by the candidate index.
local function rowMatches(ctx, rowID, skip)
	local conds, db = ctx.conds, ctx.db
	for i = 1, ctx.nConds do
		if i ~= skip then
			local cond = conds[i]
			if cond.op == OP_CUSTOM then
				if not cond.value(db, rowID) then
					return false
				end
			elseif not condMatches(cond, rowID) then
				return false
			end
		end
	end
	return true
end

-- Builds a fresh query context bound to a table (closures are created once per context).
local function newQueryContext(db)
	local ctx = setmetatable({
		db = db,
		conds = {},
		nConds = 0,
		results = {},
		n = 0,
		executed = false,
		released = false,
		sortField = nil,
		sortDesc = false,
		sortCol = nil,
		limit = nil,
		iterPos = 0,
	}, QueryMeta)
	ctx.cursor = setmetatable({ rowID = 0 }, db.cursorMeta)
	ctx.compare = function(a, b)
		local col = ctx.sortCol
		local c = compareValues(col[a], col[b])
		if c == 0 then
			return a < b
		end
		if ctx.sortDesc then
			return c > 0
		end
		return c < 0
	end
	ctx.iterFn = function()
		local i = ctx.iterPos + 1
		if i > ctx.n then
			return nil
		end
		ctx.iterPos = i
		local cursor = ctx.cursor
		cursor.rowID = ctx.results[i]
		return cursor
	end
	return ctx
end

local function addCondition(ctx, op, field, value)
	local db = ctx.db
	if ctx.released then
		dbError(db, "query context used after Release()", 4)
	end
	if field ~= nil and not db.fields[field] then
		dbError(db, format("unknown field '%s' in query", tostring(field)), 4)
	end
	local i = ctx.nConds + 1
	local cond = ctx.conds[i]
	if not cond then
		cond = {}
		ctx.conds[i] = cond
	end
	cond.op, cond.field, cond.value, cond.col = op, field, value, nil
	ctx.nConds = i
	ctx.executed = false
	return ctx
end

--- Returns a pooled query context for this table (release it with q:Release()).
function DBProto:NewQuery()
	local n = self.queryPoolN
	local ctx
	if n > 0 then
		ctx = self.queryPool[n]
		self.queryPool[n] = nil
		self.queryPoolN = n - 1
		ctx.released = false
	else
		ctx = newQueryContext(self)
	end
	return ctx
end

--- Adds the condition field == value; chainable.
function Query:Equal(field, value)
	return addCondition(self, OP_EQ, field, value)
end

--- Adds the condition field ~= value; chainable.
function Query:NotEqual(field, value)
	return addCondition(self, OP_NE, field, value)
end

--- Adds the condition field > value; chainable.
function Query:GreaterThan(field, value)
	return addCondition(self, OP_GT, field, value)
end

--- Adds the condition field >= value; chainable.
function Query:GreaterThanOrEqual(field, value)
	return addCondition(self, OP_GE, field, value)
end

--- Adds the condition field < value; chainable.
function Query:LessThan(field, value)
	return addCondition(self, OP_LT, field, value)
end

--- Adds the condition field <= value; chainable.
function Query:LessThanOrEqual(field, value)
	return addCondition(self, OP_LE, field, value)
end

--- Adds a case-insensitive substring condition on a string field; chainable.
function Query:Contains(field, substring)
	local def = self.db.fields[field]
	if not def then
		dbError(self.db, format("unknown field '%s' in query", tostring(field)), 3)
	end
	if def.type ~= "string" then
		dbError(self.db, format("Contains() requires a string field, '%s' is %s", tostring(field), def.type), 3)
	end
	return addCondition(self, OP_CONTAINS, field, strlower(tostring(substring or "")))
end

--- Adds a custom predicate fn(db, rowID) -> boolean; chainable.
function Query:Custom(fn)
	if type(fn) ~= "function" then
		dbError(self.db, "Custom() expects a function", 3)
	end
	return addCondition(self, OP_CUSTOM, nil, fn)
end

--- Sets the single sort key (stable through a rowID tiebreak); chainable.
function Query:OrderBy(field, descending)
	if self.released then
		dbError(self.db, "query context used after Release()", 3)
	end
	if not self.db.fields[field] then
		dbError(self.db, format("unknown field '%s' in OrderBy", tostring(field)), 3)
	end
	self.sortField = field
	self.sortDesc = descending and true or false
	self.executed = false
	return self
end

--- Limits the number of results; chainable.
function Query:Limit(n)
	if self.released then
		dbError(self.db, "query context used after Release()", 3)
	end
	n = tonumber(n)
	if n and n < 0 then
		n = 0
	end
	self.limit = n
	self.executed = false
	return self
end

--- Runs the query: fills q.results (rowIDs) and q.n; returns q.
function Query:Execute()
	local db = self.db
	if self.released then
		dbError(db, "query context used after Release()", 3)
	end
	local results = self.results
	for i = 1, self.n do
		results[i] = nil
	end
	local conds, nConds = self.conds, self.nConds
	local useIdx, candArr, candSingle = 0, nil, nil
	for i = 1, nConds do
		local cond = conds[i]
		if cond.field ~= nil then
			cond.col = db.cols[cond.field]
		end
		if useIdx == 0 and cond.op == OP_EQ and cond.value ~= nil then
			local umap = db.uniques[cond.field]
			if umap then
				useIdx = i
				candSingle = umap[cond.value]
			else
				local map = db.indexes[cond.field]
				if map then
					useIdx = i
					candArr = map[cond.value]
				end
			end
		end
	end
	local limit = self.limit
	local sortField = self.sortField
	local earlyStop = (limit ~= nil and sortField == nil)
	local count = 0
	if useIdx > 0 then
		if candArr then
			for i = 1, #candArr do
				local rowID = candArr[i]
				if rowMatches(self, rowID, useIdx) then
					count = count + 1
					results[count] = rowID
					if earlyStop and count >= limit then
						break
					end
				end
			end
		elseif candSingle then
			if rowMatches(self, candSingle, useIdx) and (not earlyStop or limit > 0) then
				count = 1
				results[1] = candSingle
			end
		end
	else
		for rowID = 1, db.n do
			if rowMatches(self, rowID, 0) then
				count = count + 1
				results[count] = rowID
				if earlyStop and count >= limit then
					break
				end
			end
		end
	end
	if sortField and count > 1 then
		self.sortCol = db.cols[sortField]
		tsort(results, self.compare)
		self.sortCol = nil
	end
	if limit and count > limit then
		for i = limit + 1, count do
			results[i] = nil
		end
		count = limit
	end
	self.n = count
	self.executed = true
	self.iterPos = 0
	return self
end

--- Returns an iterator closure yielding the context's reusable row cursor (executes if needed).
function Query:Iterator()
	if not self.executed then
		self:Execute()
	end
	self.iterPos = 0
	return self.iterFn
end

--- Returns the number of matching rows (executes if needed).
function Query:Count()
	if not self.executed then
		self:Execute()
	end
	return self.n
end

--- Returns the row cursor positioned on the first result, or nil (executes if needed).
function Query:First()
	if not self.executed then
		self:Execute()
	end
	if self.n < 1 then
		return nil
	end
	local cursor = self.cursor
	cursor.rowID = self.results[1]
	return cursor
end

--- Returns the context to its table's pool (results wiped).
function Query:Release()
	if self.released then
		return
	end
	local results = self.results
	for i = 1, self.n do
		results[i] = nil
	end
	local conds = self.conds
	for i = 1, self.nConds do
		local cond = conds[i]
		cond.value, cond.col, cond.field = nil, nil, nil
	end
	self.n = 0
	self.nConds = 0
	self.sortField = nil
	self.sortDesc = false
	self.sortCol = nil
	self.limit = nil
	self.executed = false
	self.iterPos = 0
	self.cursor.rowID = 0
	self.released = true
	local db = self.db
	if db.queryPoolN < QUERY_POOL_MAX then
		db.queryPoolN = db.queryPoolN + 1
		db.queryPool[db.queryPoolN] = self
	end
end

--------------------------------------------------------------------------------
-- Table definitions (SPEC §3.1)
--------------------------------------------------------------------------------
-- Field definition helper: F(type, default, index, unique, nilable)
local function F(ftype, default, index, unique, nilable)
	return {
		type = ftype,
		default = default,
		index = index and true or false,
		unique = unique and true or false,
		nilable = nilable and true or false,
	}
end

Database:New("market", {
	persistent = true,
	order = {
		"marketKey", "itemID", "itemKeyStr", "suffix", "isCommodity", "minBuyout", "marketValue",
		"historical", "numAuctions", "quantity", "lastScan", "numScans", "soldPerDay", "lastSeenQty", "lastSeenTs",
	},
	-- compact per-character blobs carry only itemID/marketValue/minBuyout/lastScan: rebuild the keys
	derive = function(row)
		local itemID = row.itemID
		if itemID == nil then
			return
		end
		if row.marketKey == nil then
			row.marketKey = currentMarketKey()
		end
		if row.itemKeyStr == nil then
			row.itemKeyStr = row.marketKey .. ":" .. tostring(itemID) .. ":" .. tostring(row.suffix or 0)
		end
		if row.numScans == nil and (row.marketValue or 0) > 0 then
			row.numScans = 1
		end
	end,
	fields = {
		marketKey = F("string", nil, true),
		itemID = F("number", nil, true),
		itemKeyStr = F("string", nil, false, true),
		suffix = F("number", 0),
		isCommodity = F("boolean", false),
		minBuyout = F("number", 0),
		marketValue = F("number", 0),
		historical = F("number", 0),
		numAuctions = F("number", 0),
		quantity = F("number", 0),
		lastScan = F("number", 0),
		numScans = F("number", 0),
		soldPerDay = F("number", 0),
		lastSeenQty = F("number", 0),
		lastSeenTs = F("number", 0),
	},
})

Database:New("history", {
	persistent = true,
	order = { "itemKeyStr", "ts", "minBuyout", "marketValue", "quantity" },
	fields = {
		itemKeyStr = F("string", nil, true),
		ts = F("number"),
		minBuyout = F("number"),
		marketValue = F("number"),
		quantity = F("number"),
	},
})

Database:New("ledger", {
	persistent = true,
	order = {
		"id", "ts", "charKey", "kind", "itemID", "itemName", "quantity", "total", "unitPrice", "other", "source", "note",
	},
	fields = {
		id = F("number", nil, false, true),
		ts = F("number", nil, true),
		charKey = F("string", nil, true),
		kind = F("string", nil, true),
		itemID = F("number", 0, true),
		itemName = F("string", ""),
		quantity = F("number", 0),
		total = F("number", 0),
		unitPrice = F("number", 0),
		other = F("string", ""),
		source = F("string", ""),
		note = F("string", ""),
	},
})

Database:New("inventory", {
	persistent = true,
	order = { "charKey", "itemID", "ikey", "bags", "bank", "mail", "auctions", "ts" },
	derive = function(row)
		if row.ikey == nil and row.charKey ~= nil and row.itemID ~= nil then
			row.ikey = row.charKey .. ":" .. tostring(row.itemID)
		end
	end,
	fields = {
		charKey = F("string", nil, true),
		itemID = F("number", nil, true),
		ikey = F("string", nil, false, true),
		bags = F("number", 0),
		bank = F("number", 0),
		mail = F("number", 0),
		auctions = F("number", 0),
		ts = F("number", 0),
	},
})

Database:New("characters", {
	persistent = true,
	order = { "charKey", "realm", "faction", "class", "money", "lastSeen", "level" },
	fields = {
		charKey = F("string", nil, false, true),
		realm = F("string"),
		faction = F("string"),
		class = F("string", ""),
		money = F("number", 0),
		lastSeen = F("number", 0),
		level = F("number", 0),
	},
})

Database:New("recipes", {
	persistent = true,
	order = {
		"recipeID", "name", "profession", "outputItemID", "numMin", "numMax", "reagentsStr", "learned", "charKey", "ts",
	},
	fields = {
		recipeID = F("number", nil, false, true),
		name = F("string", ""),
		profession = F("string", ""),
		outputItemID = F("number", 0),
		numMin = F("number", 1),
		numMax = F("number", 1),
		reagentsStr = F("string", ""),
		learned = F("boolean", true),
		charKey = F("string", ""),
		ts = F("number", 0),
	},
})

Database:New("vendor", {
	persistent = true,
	order = { "itemID", "buyPrice", "sellPrice", "ts" },
	fields = {
		itemID = F("number", nil, false, true),
		buyPrice = F("number", 0),
		sellPrice = F("number", 0),
		ts = F("number", 0),
	},
})

Database:New("sniperLog", {
	persistent = true,
	order = { "ts", "itemID", "unitPrice", "quantity", "marketValue", "reason", "bought" },
	fields = {
		ts = F("number", nil, true),
		itemID = F("number", nil, true),
		unitPrice = F("number"),
		quantity = F("number"),
		marketValue = F("number"),
		reason = F("string", ""),
		bought = F("boolean", false),
	},
})

Database:New("groups", {
	persistent = true,
	order = { "name", "itemID", "gkey" },
	derive = function(row)
		if row.gkey == nil and row.name ~= nil and row.itemID ~= nil then
			row.gkey = row.name .. ":" .. tostring(row.itemID)
		end
	end,
	fields = {
		name = F("string", nil, true),
		itemID = F("number", nil, true),
		gkey = F("string", nil, false, true),
	},
})

Database:New("auctions", {
	persistent = false,
	order = { "itemID", "suffix", "unitPrice", "quantity", "auctionID", "timeLeft", "isCommodity", "own" },
	fields = {
		itemID = F("number", nil, true),
		suffix = F("number", 0),
		unitPrice = F("number"),
		quantity = F("number"),
		auctionID = F("number", 0),
		timeLeft = F("number", 0),
		isCommodity = F("boolean", false),
		own = F("boolean", false),
	},
})

--- Shortcut table: FL.DB.<tableName> -> db instance.
FL.DB = {
	market = Database.tables.market,
	history = Database.tables.history,
	ledger = Database.tables.ledger,
	inventory = Database.tables.inventory,
	characters = Database.tables.characters,
	recipes = Database.tables.recipes,
	vendor = Database.tables.vendor,
	sniperLog = Database.tables.sniperLog,
	groups = Database.tables.groups,
	auctions = Database.tables.auctions,
}

local marketDB = Database.tables.market
local historyDB = Database.tables.history
local ledgerDB = Database.tables.ledger

--------------------------------------------------------------------------------
-- Module state shared by the registry functions and FL.Market
--------------------------------------------------------------------------------
local keyCache = {}                 -- keyCache[suffix][itemID] = itemKeyStr
local keyCacheMarket = nil          -- market key the cache was built for
local rowScratch = {}               -- reusable FindAll output (GetRow)
local historyScratch = {}           -- reusable FindAll output (history rows of one item)
local expiredScratch = {}           -- reusable list of expired history rowIDs
local recordFields = {}             -- reusable field table for market inserts
local historyFields = {}            -- reusable field table for history inserts
local lastSweepTs = 0               -- last global history sweep
local marketDirtyCount = 0          -- rows recorded since the last FL_MARKET_UPDATED
local marketFlushScheduled = false  -- a coalesced FL_MARKET_UPDATED is pending
local ledgerMaxID = nil             -- cached max ledger id
local ledgerMaxVersion = -1         -- ledger.version the cache was built against

--------------------------------------------------------------------------------
-- Registry functions: hydration, dehydration, ledger ids
--------------------------------------------------------------------------------
--- Imports every persistent table from blobs[tableName] when such a blob is present.
function Database.HydrateAll(blobs)
	if type(blobs) ~= "table" then
		blobs = nil
	end
	for name, db in pairs(Database.tables) do
		if db.persistent and blobs and type(blobs[name]) == "table" then
			db:Import(blobs[name])
		end
	end
	keyCacheMarket = nil
	lastSweepTs = 0
	ledgerMaxID = nil
end

--- Returns { tableName = db:Export() } for every persistent table.
function Database.DehydrateAll()
	local blobs = {}
	for name, db in pairs(Database.tables) do
		if db.persistent then
			blobs[name] = db:Export()
		end
	end
	return blobs
end

-- Scans the ledger id column for its maximum.
local function scanLedgerMaxID()
	local col = ledgerDB.cols.id
	local maxID = 0
	for i = 1, ledgerDB.n do
		local v = col[i]
		if v and v > maxID then
			maxID = v
		end
	end
	ledgerMaxID = maxID
	ledgerMaxVersion = ledgerDB.version
	return maxID
end

--- Returns a monotonically increasing ledger id (max existing id + 1).
function Database.NextLedgerID()
	if ledgerMaxID == nil or ledgerMaxVersion ~= ledgerDB.version then
		scanLedgerMaxID()
	end
	local candidate = ledgerMaxID + 1
	if ledgerDB.uniques.id[candidate] ~= nil then
		candidate = scanLedgerMaxID() + 1
	end
	ledgerMaxID = candidate
	return candidate
end

--------------------------------------------------------------------------------
-- FL.Market — helpers operating on FL.DB.market / FL.DB.history (SPEC §3.2)
--------------------------------------------------------------------------------
local Market = {}
FL.Market = Market

local function settingsRoot()
	return FL.Settings or (FL.RuntimeDB and FL.RuntimeDB.settings) or FL.DefaultSettings
end

local function numSetting(group, key, default)
	local root = settingsRoot()
	local g = type(root) == "table" and root[group]
	local v = type(g) == "table" and tonumber(g[key])
	if v and v > 0 then
		return v
	end
	return default
end

--------------------------------------------------------------------------------
-- Coalesced FL_MARKET_UPDATED signal
--------------------------------------------------------------------------------
local function flushMarketSignal()
	marketFlushScheduled = false
	local n = marketDirtyCount
	marketDirtyCount = 0
	if n > 0 and FL.Fire then
		FL.Fire("FL_MARKET_UPDATED", n)
	end
end

local function markMarketDirty()
	marketDirtyCount = marketDirtyCount + 1
	if marketFlushScheduled then
		return
	end
	local timer = FL.Timer
	if timer and timer.After then
		marketFlushScheduled = true
		timer.After(MARKET_SIGNAL_DELAY, flushMarketSignal)
	elseif C_Timer and C_Timer.After then
		marketFlushScheduled = true
		C_Timer.After(MARKET_SIGNAL_DELAY, flushMarketSignal)
	else
		flushMarketSignal()
	end
end

--------------------------------------------------------------------------------
-- Keys and row lookup
--------------------------------------------------------------------------------
--- Returns the market row key for an item: marketKey..":"..itemID..":"..suffix (cached per item/suffix).
function Market.KeyFor(itemID, suffix)
	local mk = currentMarketKey()
	if mk ~= keyCacheMarket then
		wipe(keyCache)
		keyCacheMarket = mk
	end
	suffix = sanitizeNumber(suffix, 0)
	local bySuffix = keyCache[suffix]
	if not bySuffix then
		bySuffix = {}
		keyCache[suffix] = bySuffix
	end
	local key = bySuffix[itemID]
	if not key then
		key = mk .. ":" .. tostring(itemID) .. ":" .. tostring(suffix)
		bySuffix[itemID] = key
	end
	return key
end
local KeyFor = Market.KeyFor

--- Returns the market rowID for itemID/suffix; with a nil suffix tries 0, then the cheapest variant for the item.
function Market.GetRow(itemID, suffix)
	itemID = tonumber(itemID)
	if not itemID then
		return nil
	end
	local umap = marketDB.uniques.itemKeyStr
	if suffix ~= nil then
		return umap[KeyFor(itemID, suffix)]
	end
	local rowID = umap[KeyFor(itemID, 0)]
	if rowID then
		return rowID
	end
	local rows = marketDB:FindAll("itemID", itemID, rowScratch)
	if rows.n == 0 then
		return nil
	end
	local mk = currentMarketKey()
	local cols = marketDB.cols
	local mkCol, mvCol = cols.marketKey, cols.marketValue
	local best, bestMV = nil, 0
	for i = 1, rows.n do
		local r = rows[i]
		if mkCol[r] == mk then
			local mv = mvCol[r] or 0
			if best == nil or (mv > 0 and (bestMV <= 0 or mv < bestMV)) then
				best, bestMV = r, mv
			end
		end
	end
	return best
end

--- Returns one market field for an item (nil when the item has no row).
function Market.Get(itemID, field, suffix)
	local rowID = Market.GetRow(itemID, suffix)
	if not rowID then
		return nil
	end
	return marketDB:Get(rowID, field)
end

--- Lowest unit buyout seen in the last scan (copper) or nil.
function Market.MinBuyout(itemID, suffix)
	return Market.Get(itemID, "minBuyout", suffix)
end

--- Smoothed market value (copper) or nil.
function Market.MarketValue(itemID, suffix)
	return Market.Get(itemID, "marketValue", suffix)
end

--- Long-horizon historical value (copper) or nil.
function Market.Historical(itemID, suffix)
	return Market.Get(itemID, "historical", suffix)
end

--- Number of auctions seen in the last scan or nil.
function Market.NumAuctions(itemID, suffix)
	return Market.Get(itemID, "numAuctions", suffix)
end

--- Estimated units sold per day or nil.
function Market.SoldPerDay(itemID, suffix)
	return Market.Get(itemID, "soldPerDay", suffix)
end

--- Unix time of the last scan that touched the item or nil.
function Market.LastScan(itemID, suffix)
	return Market.Get(itemID, "lastScan", suffix)
end

--------------------------------------------------------------------------------
-- Market value computation (index sort over parallel arrays, no per-row tables)
--------------------------------------------------------------------------------
local sortIdx = {}
local sortPrices = nil

local function idxLess(a, b)
	local pa, pb = sortPrices[a], sortPrices[b]
	if pa == pb then
		return a < b
	end
	return pa < pb
end

local function qtyAt(quantities, i)
	local q = quantities and quantities[i]
	if type(q) ~= "number" or q ~= q or q < 1 then
		return 1
	end
	return q
end

--- TSM-style market value from parallel unitPrices/quantities arrays -> marketValue, minBuyout, totalQty.
function Market.ComputeMarketValue(unitPrices, quantities, n)
	if type(unitPrices) ~= "table" then
		return 0, 0, 0
	end
	n = tonumber(n) or #unitPrices
	if type(quantities) ~= "table" then
		quantities = nil
	end
	local m, total = 0, 0
	for i = 1, n do
		local p = unitPrices[i]
		if type(p) == "number" and p > 0 then
			m = m + 1
			sortIdx[m] = i
			total = total + qtyAt(quantities, i)
		end
	end
	for i = m + 1, #sortIdx do
		sortIdx[i] = nil
	end
	if m == 0 then
		return 0, 0, 0
	end
	sortPrices = unitPrices
	if m > 1 then
		tsort(sortIdx, idxLess)
	end
	sortPrices = nil
	local minBuyout = unitPrices[sortIdx[1]]
	local limit15, limit30 = total * 0.15, total * 0.30
	local cum, sumPQ, sumQ, prev = 0, 0, 0, 0
	for k = 1, m do
		local i = sortIdx[k]
		local p = unitPrices[i]
		local q = qtyAt(quantities, i)
		local newCum = cum + q
		if k > 1 and newCum > limit15 and (newCum > limit30 or p > prev * 1.2) then
			break
		end
		sumPQ = sumPQ + p * q
		sumQ = sumQ + q
		cum = newCum
		prev = p
	end
	local marketValue = minBuyout
	if sumQ > 0 then
		marketValue = sumPQ / sumQ
	end
	return round(marketValue), minBuyout, total
end

--------------------------------------------------------------------------------
-- Sale-rate estimate and history maintenance
--------------------------------------------------------------------------------
-- Updates soldPerDay from two sightings (prevQty, then newQty after dt seconds) and
-- moves the sighting baseline to (newQty, nowTs). Quantity increases carry no sale
-- information and only move the baseline.
local function applySale(rowID, prevQty, newQty, dt, nowTs)
	local cols = marketDB.cols
	if dt > 0 and dt <= SALE_WINDOW_SEC and newQty <= prevQty then
		local sample = (prevQty - newQty) / dt * DAY_SEC
		local numScans = cols.numScans[rowID] or 1
		local halfLife = numSetting("market", "halfLifeDays", DEFAULT_HALF_LIFE_DAYS) * DAY_SEC
		local samples = numScans - 1
		if samples < 1 then
			samples = 1
		end
		local window = samples * dt
		if window > halfLife then
			window = halfLife
		end
		if window < dt then
			window = dt
		end
		local alpha = dt / window
		local old = cols.soldPerDay[rowID] or 0
		cols.soldPerDay[rowID] = old + alpha * (sample - old)
	end
	cols.lastSeenQty[rowID] = newQty
	cols.lastSeenTs[rowID] = nowTs
end

local function descLess(a, b)
	return a > b
end

-- Deletes every history row older than cutoff (descending pass keeps swap-remove safe).
local function pruneHistoryBefore(cutoff)
	local tsCol = historyDB.cols.ts
	local i = historyDB.n
	while i >= 1 do
		local ts = tsCol[i]
		if ts == nil or ts < cutoff then
			historyDB:Delete(i)
		end
		i = i - 1
	end
end

-- Global prune: retention window first, then halve the window until under the row cap.
local function sweepHistory(now, historyDays)
	lastSweepTs = now
	pruneHistoryBefore(now - historyDays * DAY_SEC)
	local days = historyDays
	while historyDB.n > HISTORY_MAX_ROWS and days > 0.25 do
		days = days / 2
		pruneHistoryBefore(now - days * DAY_SEC)
	end
end

-- Appends (or refreshes, within one bucket) the history row of an item and prunes its expired rows.
local function appendHistory(key, ts, minBuyout, marketValue, quantity)
	local historyDays = numSetting("scan", "historyDays", DEFAULT_HISTORY_DAYS)
	local cutoff = ts - historyDays * DAY_SEC
	local rows = historyDB:FindAll("itemKeyStr", key, historyScratch)
	local cols = historyDB.cols
	local tsCol = cols.ts
	local newestRow, newestTs = nil, -huge
	local nExpired = 0
	for i = 1, rows.n do
		local rowID = rows[i]
		local rts = tsCol[rowID] or 0
		if rts < cutoff then
			nExpired = nExpired + 1
			expiredScratch[nExpired] = rowID
		elseif rts > newestTs then
			newestTs = rts
			newestRow = rowID
		end
	end
	if nExpired > 0 then
		if nExpired > 1 then
			tsort(expiredScratch, descLess)
		end
		for i = 1, nExpired do
			local rowID = expiredScratch[i]
			local moved = historyDB:Delete(rowID)
			if moved and moved == newestRow then
				newestRow = rowID
			end
			expiredScratch[i] = nil
		end
	end
	if newestRow and ts >= newestTs and (ts - newestTs) < HISTORY_BUCKET_SEC then
		local prevMin = cols.minBuyout[newestRow] or 0
		if minBuyout > 0 and (prevMin <= 0 or minBuyout < prevMin) then
			cols.minBuyout[newestRow] = minBuyout
		end
		cols.marketValue[newestRow] = marketValue
		cols.quantity[newestRow] = quantity
		cols.ts[newestRow] = ts
	else
		local f = historyFields
		f.itemKeyStr = key
		f.ts = ts
		f.minBuyout = minBuyout
		f.marketValue = marketValue
		f.quantity = quantity
		historyDB:Insert(f)
	end
	if (ts - lastSweepTs) >= HISTORY_SWEEP_INTERVAL or historyDB.n > HISTORY_MAX_ROWS then
		sweepHistory(ts, historyDays)
	end
end

--------------------------------------------------------------------------------
-- Recording scans
--------------------------------------------------------------------------------
--- Upserts the market row for one scanned item (EMA smoothing) and records its history row.
function Market.Record(itemID, suffix, isCommodity, marketValueScan, minBuyout, numAuctions, quantity, ts)
	itemID = tonumber(itemID)
	if not itemID then
		return nil
	end
	suffix = sanitizeNumber(suffix, 0)
	isCommodity = isCommodity and true or false
	local mvScan = sanitizeNumber(marketValueScan, 0)
	minBuyout = sanitizeNumber(minBuyout, 0)
	numAuctions = sanitizeNumber(numAuctions, 0)
	quantity = sanitizeNumber(quantity, 0)
	ts = sanitizeNumber(ts, nil) or time()
	if minBuyout < 0 then
		minBuyout = 0
	end
	if mvScan <= 0 then
		mvScan = minBuyout
	end
	local key = KeyFor(itemID, suffix)
	local rowID = marketDB.uniques.itemKeyStr[key]
	local cols = marketDB.cols
	local storedMV
	if not rowID then
		local f = recordFields
		f.marketKey = currentMarketKey()
		f.itemID = itemID
		f.itemKeyStr = key
		f.suffix = suffix
		f.isCommodity = isCommodity
		f.minBuyout = round(minBuyout)
		f.marketValue = round(mvScan)
		f.historical = round(mvScan)
		f.numAuctions = numAuctions
		f.quantity = quantity
		f.lastScan = ts
		f.numScans = 1
		f.soldPerDay = 0
		f.lastSeenQty = quantity
		f.lastSeenTs = ts
		rowID = marketDB:Insert(f)
		storedMV = f.marketValue
	else
		local numScans = cols.numScans[rowID] or 0
		local lastScan = cols.lastScan[rowID] or 0
		local dt = ts - lastScan
		if dt < 0 then
			dt = 0
		end
		local oldMV = cols.marketValue[rowID] or 0
		local oldHist = cols.historical[rowID] or 0
		local alphaM, alphaH
		if numScans < MIN_FIRST_SCANS then
			alphaM = 1 / (numScans + 1)
			alphaH = alphaM
		else
			local halfLife = numSetting("market", "halfLifeDays", DEFAULT_HALF_LIFE_DAYS) * DAY_SEC
			local histHalfLife = numSetting("market", "historicalHalfLifeDays", DEFAULT_HIST_HALF_LIFE_DAYS) * DAY_SEC
			alphaM = 1 - 0.5 ^ (dt / halfLife)
			alphaH = 1 - 0.5 ^ (dt / histHalfLife)
		end
		local newMV, newHist
		if oldMV <= 0 then
			newMV = mvScan
		else
			newMV = oldMV + alphaM * (mvScan - oldMV)
		end
		if oldHist <= 0 then
			newHist = mvScan
		else
			newHist = oldHist + alphaH * (mvScan - oldHist)
		end
		local prevQty = cols.lastSeenQty[rowID] or 0
		local prevTs = cols.lastSeenTs[rowID] or 0
		local seenDt = 0
		if prevTs > 0 then
			seenDt = ts - prevTs
		end
		applySale(rowID, prevQty, quantity, seenDt, ts)
		storedMV = round(newMV)
		cols.marketValue[rowID] = storedMV
		cols.historical[rowID] = round(newHist)
		cols.minBuyout[rowID] = round(minBuyout)
		cols.numAuctions[rowID] = numAuctions
		cols.quantity[rowID] = quantity
		cols.lastScan[rowID] = ts
		cols.numScans[rowID] = numScans + 1
		if cols.isCommodity[rowID] ~= isCommodity then
			cols.isCommodity[rowID] = isCommodity
		end
	end
	appendHistory(key, ts, round(minBuyout), storedMV, quantity)
	markMarketDirty()
	return rowID
end

--- Updates the soldPerDay EMA from a quantity change observed within dtSeconds (only when 0 < dt <= 7200).
function Market.ApplySaleEstimate(itemID, suffix, prevQty, newQty, dtSeconds)
	local rowID = Market.GetRow(itemID, sanitizeNumber(suffix, 0))
	if not rowID then
		return false
	end
	prevQty = sanitizeNumber(prevQty, 0)
	newQty = sanitizeNumber(newQty, 0)
	local dt = sanitizeNumber(dtSeconds, 0)
	local nowTs = marketDB.cols.lastScan[rowID] or 0
	if nowTs <= 0 then
		nowTs = time()
	end
	applySale(rowID, prevQty, newQty, dt, nowTs)
	return true
end
