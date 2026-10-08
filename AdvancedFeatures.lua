local addonName, FL = ...

-------------------------------------------------------------------------------
-- AdvancedFeatures.lua
-- FL.Ledger, FL.Inventory, FL.Characters, FL.Vendor, FL.Sniper, FL.Posting,
-- FL.Crafting and FL.Intel for ForeverLedger (WoW: Forever, Interface 16001).
-- Everything here is Lua 5.1 as shipped in WoW; all Blizzard APIs that are not
-- guaranteed by SPEC §0 are existence-checked before use.
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- Cached globals
-------------------------------------------------------------------------------
local _G = _G
local pairs, ipairs, type, tonumber, tostring, select = pairs, ipairs, type, tonumber, tostring, select
local pcall, next, setmetatable, unpack = pcall, next, setmetatable, unpack
local floor, ceil, mmax, mmin, abs, huge = math.floor, math.ceil, math.max, math.min, math.abs, math.huge
local format, strlower, strfind, strmatch, gmatch, gsub, strsub, strlen = string.format, string.lower, string.find, string.match, string.gmatch, string.gsub, string.sub, string.len
local tinsert, tremove, tsort, tconcat = table.insert, table.remove, table.sort, table.concat
local wipe = wipe or function(t) for k in pairs(t) do t[k] = nil end return t end
local time, date, GetTime = time, date, GetTime
local CreateFrame, UIParent, GameTooltip = CreateFrame, UIParent, GameTooltip
local InCombatLockdown = InCombatLockdown
local GetMoney = GetMoney
local UnitName, UnitFactionGroup, UnitClass, UnitLevel = UnitName, UnitFactionGroup, UnitClass, UnitLevel
local issecretvalue = issecretvalue
local C_Item, C_Container, C_AuctionHouse = C_Item, C_Container, C_AuctionHouse
local C_TradeSkillUI, C_MerchantFrame, C_Timer = C_TradeSkillUI, C_MerchantFrame, C_Timer
local ItemLocation = ItemLocation
local hooksecurefunc = hooksecurefunc
local PlaySound, SOUNDKIT = PlaySound, SOUNDKIT
local RaidNotice_AddMessage, RaidWarningFrame, ChatTypeInfo = RaidNotice_AddMessage, RaidWarningFrame, ChatTypeInfo
local GetInboxNumItems, GetInboxHeaderInfo, GetInboxInvoiceInfo = GetInboxNumItems, GetInboxHeaderInfo, GetInboxInvoiceInfo
local GetInboxItem, GetInboxItemLink = GetInboxItem, GetInboxItemLink
local GetMerchantNumItems, GetMerchantItemInfo, GetMerchantItemLink = GetMerchantNumItems, GetMerchantItemInfo, GetMerchantItemLink
local GetNumTradeSkills, GetTradeSkillInfo, GetTradeSkillItemLink = GetNumTradeSkills, GetTradeSkillInfo, GetTradeSkillItemLink
local GetTradeSkillNumMade, GetTradeSkillNumReagents = GetTradeSkillNumMade, GetTradeSkillNumReagents
local GetTradeSkillReagentInfo, GetTradeSkillReagentItemLink = GetTradeSkillReagentInfo, GetTradeSkillReagentItemLink
local GetTradeSkillLine, GetTradeSkillRecipeLink, DoTradeSkill = GetTradeSkillLine, GetTradeSkillRecipeLink, DoTradeSkill
local GetItemCount = GetItemCount
local Enum = Enum
local ChatEdit_InsertLink, HandleModifiedItemClick = ChatEdit_InsertLink, HandleModifiedItemClick
local IsShiftKeyDown = IsShiftKeyDown

-------------------------------------------------------------------------------
-- Module tables
-------------------------------------------------------------------------------
FL.Ledger = FL.Ledger or {}
FL.Inventory = FL.Inventory or {}
FL.Characters = FL.Characters or {}
FL.Vendor = FL.Vendor or {}
FL.Sniper = FL.Sniper or {}
FL.Posting = FL.Posting or {}
FL.Crafting = FL.Crafting or {}
FL.Intel = FL.Intel or {}

local Ledger, Inventory, Characters, Vendor = FL.Ledger, FL.Inventory, FL.Characters, FL.Vendor
local Sniper, Posting, Crafting, Intel = FL.Sniper, FL.Posting, FL.Crafting, FL.Intel

-------------------------------------------------------------------------------
-- Constants
-------------------------------------------------------------------------------
local EMPTY = setmetatable({}, { __newindex = function() end })
local DAY = 86400
local SNIPER_SEEN_WINDOW = 120
local SNIPER_PASS_TIMEOUT = 20
local PRICE_SCAN_TIMEOUT = 20
local LADDER_FRESH_SEC = 15
local BAG_FIRST, BAG_LAST = 0, 4
local KEYRING_BAG = -1
local BANK_BAG_FIRST, BANK_BAG_LAST = 5, 11
local CLASS_QUEST = 12
local SOUND_RAID_WARNING = 8959
local STATUS_ACTIVE = 0

-------------------------------------------------------------------------------
-- Settings and formula helpers (file-local)
-------------------------------------------------------------------------------

-- Live settings root (falls back through RuntimeDB and defaults before hydration).
local function S()
	return FL.Settings or (FL.RuntimeDB and FL.RuntimeDB.settings) or FL.DefaultSettings or EMPTY
end

-- Sub-table of the settings root, never nil.
local function SS(name)
	local root = S()
	local sub = root and root[name]
	if type(sub) ~= "table" then
		local defaults = FL.DefaultSettings
		sub = defaults and defaults[name]
	end
	return type(sub) == "table" and sub or EMPTY
end

-- Money setting as copper (accepts numbers, "1g2s3c", "50s", "150").
local function Money(value, fallback)
	if type(value) == "number" then
		return value
	end
	if type(value) == "string" then
		local c = FL.ParseMoney and FL.ParseMoney(value)
		if type(c) == "number" then
			return c
		end
		local n = tonumber(value)
		if n then
			return n
		end
	end
	return fallback or 0
end

-- Evaluate a formula string for an item; returns a finite number or nil, err.
local function Eval(formula, itemID, suffix)
	if type(formula) ~= "string" or formula == "" or not itemID then
		return nil, "no formula"
	end
	if not (FL.Parser and FL.Parser.Evaluate) then
		return nil, "parser not loaded"
	end
	local ok, value, err = pcall(FL.Parser.Evaluate, formula, itemID, suffix or 0)
	if not ok then
		return nil, tostring(value)
	end
	if type(value) ~= "number" or value ~= value or value == huge or value == -huge then
		return nil, err
	end
	return value
end

-- Guard a unit-API return value against Midnight secret values.
local function Unsecret(v)
	if issecretvalue and v ~= nil and issecretvalue(v) then
		return nil
	end
	return v
end

-- AH cut fraction from settings.
local function AHCut()
	local cut = tonumber(SS("market").ahCut)
	if not cut then
		cut = tonumber(S().ahCut)
	end
	if not cut or cut < 0 or cut >= 1 then
		cut = 0.05
	end
	return cut
end

-- Item name with graceful fallback for unknown items.
local function ItemName(itemID)
	local name = FL.GetItemName and FL.GetItemName(itemID)
	if name then
		return name
	end
	return "item:" .. tostring(itemID)
end

-- Item link or name for chat output.
local function ItemLinkOrName(itemID)
	local link = FL.GetItemLinkCached and FL.GetItemLinkCached(itemID)
	if link then
		return link
	end
	return ItemName(itemID)
end

-- Money formatting shortcut.
local function M(copper, noColor)
	if FL.FormatMoney then
		return FL.FormatMoney(copper or 0, noColor)
	end
	return tostring(copper or 0) .. "c"
end

-- Round a unit price for posting: whole silver unless the server accepts copper.
local function RoundUnitPrice(price)
	price = floor(price)
	if C_AuctionHouse and C_AuctionHouse.SupportsCopperValues then
		local ok, supports = pcall(C_AuctionHouse.SupportsCopperValues)
		if ok and supports then
			return mmax(price, 1)
		end
	end
	price = floor(price / 100) * 100
	if price < 100 then
		price = 100
	end
	return price
end

-- Debounced call: at most one pending timer per key.
local debouncePending = {}
local function Debounce(key, delay, fn)
	if debouncePending[key] then
		return
	end
	debouncePending[key] = true
	local after = (FL.Timer and FL.Timer.After) or (C_Timer and C_Timer.After)
	if not after then
		debouncePending[key] = nil
		fn()
		return
	end
	after(delay, function()
		debouncePending[key] = nil
		fn()
	end)
end

-- Fire-and-forget timer with error reporting through FL.Timer when available.
local function After(delay, fn)
	if FL.Timer and FL.Timer.After then
		FL.Timer.After(delay, fn)
	elseif C_Timer and C_Timer.After then
		C_Timer.After(delay, function()
			local ok, err = pcall(fn)
			if not ok and FL.Warn then
				FL:Warn("Timer error: %s", tostring(err))
			end
		end)
	else
		fn()
	end
end

-- Register a game event through Core, tolerating events unknown to this client.
local function RegisterEvent(event, handler)
	if not (FL.RegisterEvent) then
		return false
	end
	local ok, err = pcall(FL.RegisterEvent, event, handler)
	if not ok and FL.Debug then
		FL:Debug("Could not register %s: %s", event, tostring(err))
	end
	return ok
end

-- Delete a set of rowIDs from a database, highest rowID first so swap-removes
-- never invalidate the remaining ids in the list.
local function DeleteRows(db, ids, n)
	n = n or #ids
	if n == 0 then
		return 0
	end
	local trimmed = ids
	if trimmed.n and trimmed.n ~= n then
		trimmed.n = n
	end
	for i = n + 1, #ids do
		ids[i] = nil
	end
	tsort(ids, function(a, b) return a > b end)
	for i = 1, n do
		db:Delete(ids[i])
	end
	return n
end

-- Realm suffix of a charKey ("Name-Realm" → "Realm"), cached per key.
local realmOfKey = {}
local function SameRealm(charKey)
	local cached = realmOfKey[charKey]
	if cached == nil then
		local realm = strmatch(charKey or "", "%-(.+)$") or ""
		realmOfKey[charKey] = realm
		cached = realm
	end
	return cached == (FL.realmKey or "Unknown")
end

-- Sort an index array by a numeric score table (desc) with stable tiebreak.
local sortScores
local function SortDescByScore(a, b)
	local sa, sb = sortScores[a], sortScores[b]
	if sa == sb then
		return a < b
	end
	return sa > sb
end

-------------------------------------------------------------------------------
-- §6.1 FL.Ledger — core API
-------------------------------------------------------------------------------
local ledgerScratch = {}
local ledgerTrimScratch = {}
local totalsOut = { sales = 0, purchases = 0, deposits = 0, consignment = 0, vendor = 0, net = 0,
	vendorSales = 0, vendorBuys = 0, income = 0, expense = 0, count = 0 }
local topAgg = {}
local topIDs = {}

-- Remove the oldest rows until the ledger is within settings.ledger.maxRows.
local function TrimLedger(db, maxRows)
	local excess = db:Count() - maxRows
	if excess <= 0 then
		return
	end
	wipe(ledgerTrimScratch)
	local q = db:NewQuery():OrderBy("ts", false):Limit(excess):Execute()
	local n = 0
	for i = 1, q.n do
		n = n + 1
		ledgerTrimScratch[n] = q.results[i]
	end
	q:Release()
	DeleteRows(db, ledgerTrimScratch, n)
end

-- FL.Ledger.Add(kind, itemID, quantity, total, other, source, note, ts) -> rowID
function Ledger.Add(kind, itemID, quantity, total, other, source, note, ts)
	local db = FL.DB and FL.DB.ledger
	if not db then
		return nil
	end
	kind = tostring(kind or "income")
	itemID = tonumber(itemID) or 0
	quantity = tonumber(quantity) or 0
	total = tonumber(total) or 0
	if total ~= total then
		total = 0
	end
	total = floor(total)
	quantity = floor(quantity)
	local unitPrice = 0
	if quantity > 0 then
		unitPrice = floor(total / quantity)
	end
	local id = FL.Database.NextLedgerID()
	local name = ""
	if itemID > 0 then
		name = FL.GetItemName and FL.GetItemName(itemID) or ""
	end
	local rowID = db:Insert({
		id = id,
		ts = tonumber(ts) or time(),
		charKey = FL.playerKey or "Unknown",
		kind = kind,
		itemID = itemID,
		itemName = name,
		quantity = quantity,
		total = total,
		unitPrice = unitPrice,
		other = tostring(other or ""),
		source = tostring(source or ""),
		note = tostring(note or ""),
	})
	if name == "" and itemID > 0 and FL.RequestItem then
		FL.RequestItem(itemID, function(loadedID)
			local resolved = FL.GetItemName and FL.GetItemName(loadedID)
			if resolved then
				local rid = db:FindFirst("id", id)
				if rid then
					db:Set(rid, "itemName", resolved)
				end
			end
		end)
	end
	local maxRows = tonumber(SS("ledger").maxRows) or 5000
	if maxRows > 0 and db:Count() > maxRows then
		TrimLedger(db, maxRows)
		rowID = db:FindFirst("id", id)
	end
	FL.Fire("FL_LEDGER_CHANGED", kind, rowID, itemID)
	return rowID
end

-- Weighted average unit price over rows of one kind for an item (nil when none).
local function WeightedAverage(itemID, kind)
	local db = FL.DB and FL.DB.ledger
	if not db or not itemID then
		return nil
	end
	db:FindAll("itemID", itemID, ledgerScratch)
	local sumTotal, sumQty = 0, 0
	for i = 1, ledgerScratch.n or #ledgerScratch do
		local rid = ledgerScratch[i]
		if db:Get(rid, "kind") == kind then
			local total = db:Get(rid, "total")
			local qty = db:Get(rid, "quantity")
			if total > 0 and qty > 0 then
				sumTotal = sumTotal + total
				sumQty = sumQty + qty
			end
		end
	end
	if sumQty <= 0 then
		return nil
	end
	return floor(sumTotal / sumQty)
end

-- FL.Ledger.AvgBuy(itemID) -> copper|nil (quantity-weighted over "purchase" rows)
function Ledger.AvgBuy(itemID)
	return WeightedAverage(itemID, "purchase")
end

-- FL.Ledger.AvgSell(itemID) -> copper|nil (quantity-weighted over "sale" rows)
function Ledger.AvgSell(itemID)
	return WeightedAverage(itemID, "sale")
end

-- FL.Ledger.Totals(sinceTs) -> { sales, purchases, deposits, consignment, vendor, net } (reused table)
function Ledger.Totals(sinceTs)
	local out = totalsOut
	out.sales, out.purchases, out.deposits, out.consignment = 0, 0, 0, 0
	out.vendorSales, out.vendorBuys, out.income, out.expense, out.count = 0, 0, 0, 0, 0
	local db = FL.DB and FL.DB.ledger
	if db then
		local q = db:NewQuery()
		if sinceTs and sinceTs > 0 then
			q:GreaterThanOrEqual("ts", sinceTs)
		end
		for c in q:Iterator() do
			local kind, total = c.kind, c.total
			out.count = out.count + 1
			if kind == "sale" then
				out.sales = out.sales + total
			elseif kind == "purchase" then
				out.purchases = out.purchases + total
			elseif kind == "deposit" then
				out.deposits = out.deposits + total
			elseif kind == "consignment" then
				out.consignment = out.consignment + total
			elseif kind == "vendorsale" then
				out.vendorSales = out.vendorSales + total
			elseif kind == "vendorbuy" then
				out.vendorBuys = out.vendorBuys + total
			elseif kind == "income" then
				out.income = out.income + total
			elseif kind == "expense" then
				out.expense = out.expense + total
			end
		end
		q:Release()
	end
	out.vendor = out.vendorSales - out.vendorBuys
	out.net = out.sales + out.income + out.vendor - out.purchases - out.deposits - out.consignment - out.expense
	return out
end

-- FL.Ledger.TopItems(sinceTs, kind, limit, out) -> out (array of {itemID, quantity, total}, out.n set)
function Ledger.TopItems(sinceTs, kind, limit, out)
	out = out or {}
	limit = tonumber(limit) or 10
	kind = kind or "sale"
	wipe(topAgg)
	wipe(topIDs)
	local db = FL.DB and FL.DB.ledger
	local nIDs = 0
	if db then
		local q = db:NewQuery():Equal("kind", kind)
		if sinceTs and sinceTs > 0 then
			q:GreaterThanOrEqual("ts", sinceTs)
		end
		for c in q:Iterator() do
			local itemID = c.itemID
			if itemID and itemID > 0 then
				local agg = topAgg[itemID]
				if not agg then
					nIDs = nIDs + 1
					topIDs[nIDs] = itemID
					agg = { quantity = 0, total = 0 }
					topAgg[itemID] = agg
				end
				agg.quantity = agg.quantity + (c.quantity or 0)
				agg.total = agg.total + (c.total or 0)
			end
		end
		q:Release()
	end
	tsort(topIDs, function(a, b)
		local ta, tb = topAgg[a].total, topAgg[b].total
		if ta == tb then
			return a < b
		end
		return ta > tb
	end)
	local n = mmin(nIDs, limit)
	for i = 1, n do
		local itemID = topIDs[i]
		local entry = out[i]
		if type(entry) ~= "table" then
			entry = {}
			out[i] = entry
		end
		entry.itemID = itemID
		entry.quantity = topAgg[itemID].quantity
		entry.total = topAgg[itemID].total
		entry.name = ItemName(itemID)
	end
	for i = n + 1, #out do
		out[i] = nil
	end
	out.n = n
	return out
end

-- Look up an itemID from a plain item name using ledger rows (nil when unknown).
local nameLookupCache = {}
local function ItemIDByName(name)
	if type(name) ~= "string" or name == "" then
		return nil
	end
	local cached = nameLookupCache[name]
	if cached then
		return cached
	end
	local db = FL.DB and FL.DB.ledger
	if db then
		local q = db:NewQuery():Equal("itemName", name):Limit(1):Execute()
		local c = q:First()
		local found = c and c.itemID
		q:Release()
		if found and found > 0 then
			nameLookupCache[name] = found
			return found
		end
	end
	local queue = Posting.queue
	if queue then
		for i = 1, #queue do
			if queue[i].name == name then
				nameLookupCache[name] = queue[i].itemID
				return queue[i].itemID
			end
		end
	end
	return nil
end

-------------------------------------------------------------------------------
-- §6.1 FL.Ledger — mail invoice source
-------------------------------------------------------------------------------
local mailSeen = {}
local mailOpen = false
local mailCounts = {}
local mailDedupeScratch = {}

-- True when a ledger row with this dedupe note already exists for the item.
local function LedgerHasNote(itemID, note)
	local db = FL.DB and FL.DB.ledger
	if not db then
		return false
	end
	if itemID and itemID > 0 then
		db:FindAll("itemID", itemID, mailDedupeScratch)
		for i = 1, mailDedupeScratch.n or #mailDedupeScratch do
			if db:Get(mailDedupeScratch[i], "note") == note then
				return true
			end
		end
		return false
	end
	local q = db:NewQuery():Equal("note", note):Limit(1)
	local found = q:Count() > 0
	q:Release()
	return found
end

-- Process one inbox entry that carries an auction invoice.
local function ProcessInvoice(index, sender, subject, money, daysLeft)
	local invoiceType, itemName, playerName, bid, buyout, deposit, consignment, _, _, _, count = GetInboxInvoiceInfo(index)
	if not invoiceType then
		return
	end
	bid = tonumber(bid) or 0
	buyout = tonumber(buyout) or 0
	deposit = tonumber(deposit) or 0
	consignment = tonumber(consignment) or 0
	count = tonumber(count) or 1
	if count < 1 then
		count = 1
	end
	local ageDays = 30 - (tonumber(daysLeft) or 30)
	if ageDays < 0 then
		ageDays = 0
	end
	local ts = time() - floor(ageDays * DAY)
	local day = floor(ts / DAY)
	local key = tostring(sender or "") .. "|" .. tostring(subject or "") .. "|" .. tostring(money or 0) .. "|" .. tostring(day) .. "|" .. tostring(bid)
	if mailSeen[key] then
		return
	end
	mailSeen[key] = true
	local itemID = 0
	if GetInboxItemLink then
		local link = GetInboxItemLink(index, 1)
		itemID = link and FL.ItemIDFromLink(link) or 0
	end
	if itemID == 0 then
		itemID = ItemIDByName(itemName) or 0
	end
	local note = "mail:" .. key
	if LedgerHasNote(itemID, note) then
		return
	end
	local amount = bid > 0 and bid or buyout
	if invoiceType == "seller" or invoiceType == "seller_temp_invoice" then
		Ledger.Add("sale", itemID, count, amount, tostring(playerName or ""), "mail", note, ts)
		if consignment > 0 then
			Ledger.Add("consignment", itemID, count, consignment, tostring(playerName or ""), "mail", note, ts)
		end
		if deposit > 0 then
			Ledger.Add("income", itemID, count, deposit, "deposit refund", "mail", note, ts)
		end
	elseif invoiceType == "buyer" then
		Ledger.Add("purchase", itemID, count, amount, tostring(playerName or ""), "mail", note, ts)
	end
end

-- Count attached items in the inbox per itemID and mirror them into inventory.mail.
local function ScanMailInventory()
	if not (GetInboxNumItems and GetInboxItem) then
		return
	end
	wipe(mailCounts)
	local n = GetInboxNumItems() or 0
	local maxAttach = _G.ATTACHMENTS_MAX_RECEIVE or 16
	for i = 1, n do
		for j = 1, maxAttach do
			local name, itemID, _, count = GetInboxItem(i, j)
			if name and itemID then
				mailCounts[itemID] = (mailCounts[itemID] or 0) + (tonumber(count) or 1)
			end
		end
	end
	Inventory.ApplyMail(mailCounts)
end

-- Walk the inbox for auction invoices (MAIL_SHOW / MAIL_INBOX_UPDATE).
local function OnMailInboxUpdate()
	if not SS("ledger").trackMail then
		return
	end
	if not (GetInboxNumItems and GetInboxHeaderInfo and GetInboxInvoiceInfo) then
		return
	end
	local n = GetInboxNumItems() or 0
	for i = 1, n do
		local _, _, sender, subject, money, _, daysLeft, _, _, _, _, _, _ = GetInboxHeaderInfo(i)
		if sender then
			local ok, err = pcall(ProcessInvoice, i, sender, subject, money, daysLeft)
			if not ok then
				FL:Debug("Invoice parse failed for mail %d: %s", i, tostring(err))
			end
		end
	end
	ScanMailInventory()
end

-------------------------------------------------------------------------------
-- §6.1 FL.Ledger — CHAT_MSG_SYSTEM source
-------------------------------------------------------------------------------
local chatPatterns = {}
local chatPatternCount = 0

-- Convert a Blizzard format string into a Lua pattern with (.+) captures.
local function GlobalStringToPattern(str)
	if type(str) ~= "string" or str == "" then
		return nil
	end
	local escaped = gsub(str, "([%^%$%(%)%%%.%[%]%*%+%-%?])", "%%%1")
	escaped = gsub(escaped, "%%%%%d+%%%$s", "(.+)")
	escaped = gsub(escaped, "%%%%s", "(.+)")
	escaped = gsub(escaped, "%%%%%d+%%%$d", "(%%d+)")
	escaped = gsub(escaped, "%%%%d", "(%%d+)")
	return "^" .. escaped .. "$"
end

-- Build chat patterns from ERR_AUCTION_* once the globals are loaded.
local function BuildChatPatterns()
	wipe(chatPatterns)
	chatPatternCount = 0
	local sources = {
		{ "ERR_AUCTION_SOLD_S", "sale" },
		{ "ERR_AUCTION_EXPIRED_S", "expired" },
		{ "ERR_AUCTION_REMOVED_S", "cancelled" },
		{ "ERR_AUCTION_WON_S", "purchase" },
	}
	for i = 1, #sources do
		local pattern = GlobalStringToPattern(_G[sources[i][1]])
		if pattern then
			chatPatternCount = chatPatternCount + 1
			chatPatterns[chatPatternCount] = { pattern = pattern, kind = sources[i][2] }
		end
	end
end

-- Match an auction system message and record the matching ledger row.
local function OnChatSystem(_, msg)
	if type(msg) ~= "string" or chatPatternCount == 0 then
		return
	end
	for i = 1, chatPatternCount do
		local entry = chatPatterns[i]
		local captured = strmatch(msg, entry.pattern)
		if captured then
			local itemID = FL.ItemIDFromLink(captured) or ItemIDByName(captured) or 0
			local kind = entry.kind
			if kind == "sale" then
				Ledger.Add("sale", itemID, 0, 0, "", "chat", "chat")
			elseif kind == "purchase" then
				Ledger.Add("purchase", itemID, 0, 0, "", "chat", "chat")
			else
				Ledger.Add(kind, itemID, 0, 0, "", "chat", "chat")
			end
			return
		end
	end
end

-------------------------------------------------------------------------------
-- §6.1 FL.Ledger — vendor source (merchant diffing + BuyMerchantItem hook)
-------------------------------------------------------------------------------
local merchantOpen = false
local merchantSnapshot = {}
local merchantCurrent = {}
local merchantSellPrice = {}
local merchantHooked = false
local pendingVendorBuys = {}

-- Count bag contents per itemID into out (reused) and remember sell prices.
local function SnapshotBags(out)
	wipe(out)
	if not (C_Container and C_Container.GetContainerNumSlots and C_Container.GetContainerItemInfo) then
		return out
	end
	for bag = BAG_FIRST, BAG_LAST do
		local slots = C_Container.GetContainerNumSlots(bag) or 0
		for slot = 1, slots do
			local info = C_Container.GetContainerItemInfo(bag, slot)
			if info and info.itemID then
				local itemID = info.itemID
				out[itemID] = (out[itemID] or 0) + (info.stackCount or 1)
				if not merchantSellPrice[itemID] then
					local sell = Vendor.SellPrice(itemID)
					if sell then
						merchantSellPrice[itemID] = sell
					end
				end
			end
		end
	end
	return out
end

-- Diff bags against the merchant-open snapshot and record vendor sales.
local function DiffMerchantBags()
	if not merchantOpen then
		return
	end
	SnapshotBags(merchantCurrent)
	if SS("ledger").trackVendor then
		for itemID, oldCount in pairs(merchantSnapshot) do
			local newCount = merchantCurrent[itemID] or 0
			if newCount < oldCount then
				local sold = oldCount - newCount
				local sell = merchantSellPrice[itemID] or Vendor.SellPrice(itemID) or 0
				if sell > 0 then
					Ledger.Add("vendorsale", itemID, sold, sell * sold, "", "vendor", "")
				end
			end
		end
	end
	merchantSnapshot, merchantCurrent = merchantCurrent, merchantSnapshot
end

-- Record a vendor purchase from the BuyMerchantItem hook.
local function OnBuyMerchantItem(index, quantity)
	if not merchantOpen or not SS("ledger").trackVendor then
		return
	end
	index = tonumber(index)
	if not index then
		return
	end
	local price, stackCount, extended, currencyID
	if C_MerchantFrame and C_MerchantFrame.GetItemInfo then
		local info = C_MerchantFrame.GetItemInfo(index)
		if info then
			price, stackCount, extended, currencyID = info.price, info.stackCount, info.hasExtendedCost, info.currencyID
		end
	elseif GetMerchantItemInfo then
		local _, _, p, sc, _, _, _, ext, cur = GetMerchantItemInfo(index)
		price, stackCount, extended, currencyID = p, sc, ext, cur
	end
	if not price or extended or (currencyID and currencyID ~= 0) then
		return
	end
	local link = GetMerchantItemLink and GetMerchantItemLink(index)
	local itemID = link and FL.ItemIDFromLink(link)
	if not itemID then
		return
	end
	stackCount = tonumber(stackCount) or 1
	if stackCount < 1 then
		stackCount = 1
	end
	local units = tonumber(quantity) or stackCount
	if units < 1 then
		units = stackCount
	end
	local total = floor(price * units / stackCount)
	if total > 0 then
		Ledger.Add("vendorbuy", itemID, units, total, "", "vendor", "")
		pendingVendorBuys[itemID] = (pendingVendorBuys[itemID] or 0) + units
	end
end

-- Capture the item under the cursor click so sell prices are known before the bag changes.
local function OnUseContainerItem(bag, slot)
	if not merchantOpen then
		return
	end
	if not (C_Container and C_Container.GetContainerItemInfo) then
		return
	end
	local ok, info = pcall(C_Container.GetContainerItemInfo, bag, slot)
	if ok and info and info.itemID and not merchantSellPrice[info.itemID] then
		local sell = Vendor.SellPrice(info.itemID)
		if sell then
			merchantSellPrice[info.itemID] = sell
		end
	end
end

-- Install the secure hooks exactly once.
local function InstallMerchantHooks()
	if merchantHooked or not hooksecurefunc then
		return
	end
	merchantHooked = true
	if C_Container and C_Container.UseContainerItem then
		pcall(hooksecurefunc, C_Container, "UseContainerItem", OnUseContainerItem)
	elseif _G.UseContainerItem then
		pcall(hooksecurefunc, "UseContainerItem", OnUseContainerItem)
	end
	if _G.BuyMerchantItem then
		pcall(hooksecurefunc, "BuyMerchantItem", OnBuyMerchantItem)
	end
	if C_MerchantFrame and C_MerchantFrame.BuyMerchantItem then
		pcall(hooksecurefunc, C_MerchantFrame, "BuyMerchantItem", OnBuyMerchantItem)
	end
end

-------------------------------------------------------------------------------
-- §6.1 FL.Ledger — auction deposit source
-------------------------------------------------------------------------------
-- Record the deposit for the auction that was just created from Posting.lastPost.
local function OnAuctionCreatedLedger()
	local last = Posting.lastPost
	if not last or last.ledgered then
		return
	end
	last.ledgered = true
	local deposit = tonumber(last.deposit) or 0
	if deposit > 0 then
		Ledger.Add("deposit", last.itemID, last.quantity or 0, deposit, "", "ah", "")
	end
end

-------------------------------------------------------------------------------
-- §6.2 FL.Inventory
-------------------------------------------------------------------------------
local bankOpen = false
local invCounts = {}
local invRows = {}
local invTotalScratch = {}
local invEachScratch = {}
local invZeroScratch = {}

-- Write one column (bags/bank/mail/auctions) for this character from a count map.
local function ApplyInventoryColumn(column, counts)
	local db = FL.DB and FL.DB.inventory
	local charKey = FL.playerKey
	if not db or not charKey or charKey == "Unknown" then
		return
	end
	local now = time()
	db:FindAll("charKey", charKey, invRows)
	local nZero = 0
	wipe(invZeroScratch)
	for i = 1, invRows.n or #invRows do
		local rid = invRows[i]
		local itemID = db:Get(rid, "itemID")
		local newCount = counts[itemID]
		if newCount then
			if db:Get(rid, column) ~= newCount then
				db:Set(rid, column, newCount)
				db:Set(rid, "ts", now)
			end
			counts[itemID] = nil
		elseif db:Get(rid, column) ~= 0 then
			db:Set(rid, column, 0)
			db:Set(rid, "ts", now)
		end
		if db:Get(rid, "bags") == 0 and db:Get(rid, "bank") == 0 and db:Get(rid, "mail") == 0 and db:Get(rid, "auctions") == 0 then
			nZero = nZero + 1
			invZeroScratch[nZero] = rid
		end
	end
	for itemID, count in pairs(counts) do
		if count > 0 then
			local ikey = charKey .. ":" .. itemID
			db:Upsert("ikey", ikey, { charKey = charKey, itemID = itemID, ikey = ikey, [column] = count, ts = now })
		end
	end
	if nZero > 0 then
		DeleteRows(db, invZeroScratch, nZero)
	end
	FL.Fire("FL_INVENTORY_CHANGED", column)
end

-- Count items in a bag range into counts (reused map).
local function CountBags(counts, firstBag, lastBag)
	if not (C_Container and C_Container.GetContainerNumSlots and C_Container.GetContainerItemInfo) then
		return counts
	end
	for bag = firstBag, lastBag do
		local slots = C_Container.GetContainerNumSlots(bag) or 0
		for slot = 1, slots do
			local info = C_Container.GetContainerItemInfo(bag, slot)
			if info and info.itemID then
				counts[info.itemID] = (counts[info.itemID] or 0) + (info.stackCount or 1)
			end
		end
	end
	return counts
end

-- FL.Inventory.ScanBags() -- bags 0..4 → inventory rows for FL.playerKey
function Inventory.ScanBags()
	wipe(invCounts)
	CountBags(invCounts, BAG_FIRST, BAG_LAST)
	ApplyInventoryColumn("bags", invCounts)
end

-- FL.Inventory.ScanBank() -- keyring + bank bags while the bank is open
function Inventory.ScanBank()
	if not bankOpen then
		return
	end
	wipe(invCounts)
	CountBags(invCounts, KEYRING_BAG, KEYRING_BAG)
	CountBags(invCounts, BANK_BAG_FIRST, BANK_BAG_LAST)
	if Enum and Enum.BagIndex and Enum.BagIndex.Characterbanktab then
		CountBags(invCounts, Enum.BagIndex.Characterbanktab, Enum.BagIndex.Characterbanktab)
	end
	ApplyInventoryColumn("bank", invCounts)
end

-- FL.Inventory.ApplyMail(counts) -- inbox attachment counts per itemID for this character
function Inventory.ApplyMail(counts)
	wipe(invCounts)
	for itemID, count in pairs(counts) do
		invCounts[itemID] = count
	end
	ApplyInventoryColumn("mail", invCounts)
end

-- FL.Inventory.UpdateAuctions(ownedArray) -- active owned auctions → inventory.auctions
function Inventory.UpdateAuctions(ownedArray)
	wipe(invCounts)
	if type(ownedArray) == "table" then
		for i = 1, #ownedArray do
			local a = ownedArray[i]
			local itemID = a and a.itemKey and a.itemKey.itemID
			if itemID and (a.status == nil or a.status == STATUS_ACTIVE) then
				invCounts[itemID] = (invCounts[itemID] or 0) + (a.quantity or 1)
			end
		end
	end
	ApplyInventoryColumn("auctions", invCounts)
end

-- FL.Inventory.Total(itemID) -> total, bags, bank, mail, auctions (all characters on this realm)
function Inventory.Total(itemID)
	local db = FL.DB and FL.DB.inventory
	if not db or not itemID then
		return 0, 0, 0, 0, 0
	end
	db:FindAll("itemID", itemID, invTotalScratch)
	local bags, bank, mail, auctions = 0, 0, 0, 0
	for i = 1, invTotalScratch.n or #invTotalScratch do
		local rid = invTotalScratch[i]
		if SameRealm(db:Get(rid, "charKey")) then
			bags = bags + db:Get(rid, "bags")
			bank = bank + db:Get(rid, "bank")
			mail = mail + db:Get(rid, "mail")
			auctions = auctions + db:Get(rid, "auctions")
		end
	end
	return bags + bank + mail + auctions, bags, bank, mail, auctions
end

-- FL.Inventory.Here(itemID) -> bag count on this character (live when the API is available)
function Inventory.Here(itemID)
	if not itemID then
		return 0
	end
	if C_Item and C_Item.GetItemCount then
		local ok, count = pcall(C_Item.GetItemCount, itemID, false, false, false, false)
		if ok and type(count) == "number" then
			return count
		end
	end
	if GetItemCount then
		local ok, count = pcall(GetItemCount, itemID)
		if ok and type(count) == "number" then
			return count
		end
	end
	local db = FL.DB and FL.DB.inventory
	if db and FL.playerKey then
		local rid = db:FindFirst("ikey", FL.playerKey .. ":" .. itemID)
		if rid then
			return db:Get(rid, "bags")
		end
	end
	return 0
end

-- FL.Inventory.ForEachCharacter(itemID, fn) -- fn(charKey, bags, bank, mail, auctions)
function Inventory.ForEachCharacter(itemID, fn)
	local db = FL.DB and FL.DB.inventory
	if not db or not itemID or type(fn) ~= "function" then
		return
	end
	db:FindAll("itemID", itemID, invEachScratch)
	for i = 1, invEachScratch.n or #invEachScratch do
		local rid = invEachScratch[i]
		if fn(db:Get(rid, "charKey"), db:Get(rid, "bags"), db:Get(rid, "bank"), db:Get(rid, "mail"), db:Get(rid, "auctions")) then
			break
		end
	end
end

-------------------------------------------------------------------------------
-- §6.2 FL.Characters
-------------------------------------------------------------------------------
-- FL.Characters.Touch() -- upsert this character's money/level/class/realm/faction
function Characters.Touch()
	local db = FL.DB and FL.DB.characters
	local charKey = FL.playerKey
	if not db or not charKey or charKey == "Unknown" then
		return
	end
	local classFile
	if UnitClass then
		local _, cf = UnitClass("player")
		classFile = Unsecret(cf)
	end
	local level = UnitLevel and Unsecret(UnitLevel("player"))
	local money = GetMoney and GetMoney() or 0
	if type(level) ~= "number" then
		level = 0
	end
	if type(money) ~= "number" then
		money = 0
	end
	db:Upsert("charKey", charKey, {
		charKey = charKey,
		realm = FL.realmKey or "Unknown",
		faction = FL.factionKey or "Neutral",
		class = type(classFile) == "string" and classFile or "",
		money = money,
		lastSeen = time(),
		level = level,
	})
end

-- FL.Characters.TotalGold() -> copper across characters on this realm
function Characters.TotalGold()
	local db = FL.DB and FL.DB.characters
	if not db then
		return GetMoney and GetMoney() or 0
	end
	local total = 0
	local realm = FL.realmKey or "Unknown"
	db:ForEach(function(rid)
		if db:Get(rid, "realm") == realm then
			total = total + (db:Get(rid, "money") or 0)
		end
	end)
	return total
end

-------------------------------------------------------------------------------
-- §6.3 FL.Vendor
-------------------------------------------------------------------------------
local vendorFields = {}

-- Record unlimited-stock merchant prices into the vendor table.
local function RecordMerchant()
	local db = FL.DB and FL.DB.vendor
	if not db or not GetMerchantNumItems then
		return
	end
	local n = GetMerchantNumItems() or 0
	local now = time()
	local recorded = 0
	for i = 1, n do
		local price, stackCount, numAvailable, extended, currencyID
		if C_MerchantFrame and C_MerchantFrame.GetItemInfo then
			local info = C_MerchantFrame.GetItemInfo(i)
			if info then
				price, stackCount, numAvailable, extended, currencyID = info.price, info.stackCount, info.numAvailable, info.hasExtendedCost, info.currencyID
			end
		elseif GetMerchantItemInfo then
			local _, _, p, sc, na, _, _, ext, cur = GetMerchantItemInfo(i)
			price, stackCount, numAvailable, extended, currencyID = p, sc, na, ext, cur
		end
		if price and price > 0 and numAvailable == -1 and not extended and (not currencyID or currencyID == 0) then
			local link = GetMerchantItemLink and GetMerchantItemLink(i)
			local itemID = link and FL.ItemIDFromLink(link)
			if itemID then
				stackCount = tonumber(stackCount) or 1
				if stackCount < 1 then
					stackCount = 1
				end
				wipe(vendorFields)
				vendorFields.itemID = itemID
				vendorFields.buyPrice = floor(price / stackCount)
				vendorFields.ts = now
				local sell = FL.GetItemSellPrice and FL.GetItemSellPrice(itemID)
				if sell and sell > 0 then
					vendorFields.sellPrice = sell
				end
				db:Upsert("itemID", itemID, vendorFields)
				recorded = recorded + 1
			end
		end
	end
	if recorded > 0 then
		FL:Debug("Recorded %d vendor prices", recorded)
	end
end

-- FL.Vendor.BuyPrice(itemID) -> copper|nil (unlimited-stock vendor price per unit)
function Vendor.BuyPrice(itemID)
	local db = FL.DB and FL.DB.vendor
	if not db or not itemID then
		return nil
	end
	local rid = db:FindFirst("itemID", itemID)
	if rid then
		local price = db:Get(rid, "buyPrice")
		if price and price > 0 then
			return price
		end
	end
	return nil
end

-- FL.Vendor.SellPrice(itemID) -> copper|nil (vendor table, falling back to item data)
function Vendor.SellPrice(itemID)
	if not itemID then
		return nil
	end
	local db = FL.DB and FL.DB.vendor
	if db then
		local rid = db:FindFirst("itemID", itemID)
		if rid then
			local price = db:Get(rid, "sellPrice")
			if price and price > 0 then
				return price
			end
		end
	end
	local sell = FL.GetItemSellPrice and FL.GetItemSellPrice(itemID)
	if sell and sell > 0 then
		return sell
	end
	return nil
end

-------------------------------------------------------------------------------
-- §6.4 FL.Sniper — state
-------------------------------------------------------------------------------
Sniper.classRotation = { 0, 1, 2, 3, 4, 7, 9, 12, 15 }
Sniper.stats = Sniper.stats or { passes = 0, deals = 0, bought = 0, lastPassAt = 0 }
Sniper.seen = Sniper.seen or {}
Sniper.dealQueue = Sniper.dealQueue or {}
Sniper.lastDeal = nil
Sniper.currentDeal = nil

local sniperRunning = false
local sniperInPass = false
local rotationIndex = 0
local passToken = 0
local buyToken = 0
local evaluatedInPass = {}
local popup
local popupNeedsAttach = false

-------------------------------------------------------------------------------
-- §6.4 FL.Sniper — native popup frame
-------------------------------------------------------------------------------
local POPUP_BACKDROP = {
	bgFile = "Interface\\DialogFrame\\UI-DialogBox-Background",
	edgeFile = "Interface\\DialogFrame\\UI-DialogBox-Border",
	tile = true, tileSize = 32, edgeSize = 32,
	insets = { left = 11, right = 12, top = 12, bottom = 11 },
}

-- Re-parent the secure buy button into the popup (out of combat only).
local function AttachBuyButton()
	if not popup or not (FL.Secure and FL.Secure.Attach) then
		return false
	end
	if InCombatLockdown() then
		popupNeedsAttach = true
		return false
	end
	popupNeedsAttach = false
	local ok, err = pcall(FL.Secure.Attach, "buy", popup, "BOTTOMLEFT", "BOTTOMLEFT", 16, 16, 150, 24)
	if not ok then
		FL:Debug("Attach buy button failed: %s", tostring(err))
		return false
	end
	return true
end

-- Set the popup's status line.
local function PopupStatus(text, r, g, b)
	if popup and popup.status then
		popup.status:SetText(text or "")
		popup.status:SetTextColor(r or 0.8, g or 0.8, b or 0.8)
	end
end

-- Build the popup frame lazily (never in combat).
local function CreatePopup()
	if popup then
		return popup
	end
	if InCombatLockdown() then
		return nil
	end
	local ok, f = pcall(CreateFrame, "Frame", nil, UIParent, "BackdropTemplate")
	if not ok or not f then
		f = CreateFrame("Frame", nil, UIParent)
	end
	f:SetSize(360, 200)
	f:SetPoint("CENTER", UIParent, "CENTER", 0, 160)
	f:SetFrameStrata("DIALOG")
	f:SetToplevel(true)
	f:SetClampedToScreen(true)
	f:EnableMouse(true)
	f:SetMovable(true)
	f:RegisterForDrag("LeftButton")
	f:SetScript("OnDragStart", function(self) self:StartMoving() end)
	f:SetScript("OnDragStop", function(self) self:StopMovingOrSizing() end)
	if f.SetBackdrop then
		f:SetBackdrop(POPUP_BACKDROP)
		f:SetBackdropColor(0.05, 0.05, 0.08, 0.95)
	else
		local bg = f:CreateTexture(nil, "BACKGROUND")
		bg:SetAllPoints(f)
		bg:SetColorTexture(0.05, 0.05, 0.08, 0.95)
	end
	f:Hide()

	local title = f:CreateFontString(nil, "OVERLAY", "GameFontNormal")
	title:SetPoint("TOP", f, "TOP", 0, -14)
	title:SetText("|cff33ff99ForeverLedger|r Sniper")
	f.title = title

	local close = CreateFrame("Button", nil, f, "UIPanelCloseButton")
	close:SetPoint("TOPRIGHT", f, "TOPRIGHT", -6, -6)
	close:SetScript("OnClick", function() Sniper:Skip() end)
	f.close = close

	local icon = f:CreateTexture(nil, "ARTWORK")
	icon:SetSize(36, 36)
	icon:SetPoint("TOPLEFT", f, "TOPLEFT", 18, -34)
	icon:SetTexCoord(0.07, 0.93, 0.07, 0.93)
	f.icon = icon

	local nameBtn = CreateFrame("Button", nil, f)
	nameBtn:SetPoint("TOPLEFT", icon, "TOPRIGHT", 8, 0)
	nameBtn:SetSize(270, 18)
	local name = nameBtn:CreateFontString(nil, "OVERLAY", "GameFontHighlight")
	name:SetPoint("LEFT", nameBtn, "LEFT", 0, 0)
	name:SetWidth(270)
	name:SetJustifyH("LEFT")
	name:SetWordWrap(false)
	nameBtn:SetScript("OnEnter", function(self)
		local deal = Sniper.currentDeal
		local link = deal and FL.GetItemLinkCached and FL.GetItemLinkCached(deal.itemID)
		if link and GameTooltip then
			GameTooltip:SetOwner(self, "ANCHOR_RIGHT")
			GameTooltip:SetHyperlink(link)
			GameTooltip:Show()
		end
	end)
	nameBtn:SetScript("OnLeave", function()
		if GameTooltip then
			GameTooltip:Hide()
		end
	end)
	nameBtn:SetScript("OnClick", function()
		local deal = Sniper.currentDeal
		local link = deal and FL.GetItemLinkCached and FL.GetItemLinkCached(deal.itemID)
		if link and IsShiftKeyDown and IsShiftKeyDown() then
			if HandleModifiedItemClick then
				HandleModifiedItemClick(link)
			elseif ChatEdit_InsertLink then
				ChatEdit_InsertLink(link)
			end
		end
	end)
	f.name = name

	local price = f:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
	price:SetPoint("TOPLEFT", nameBtn, "BOTTOMLEFT", 0, -2)
	price:SetWidth(270)
	price:SetJustifyH("LEFT")
	f.price = price

	local profit = f:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
	profit:SetPoint("TOPLEFT", f, "TOPLEFT", 18, -78)
	profit:SetWidth(320)
	profit:SetJustifyH("LEFT")
	f.profit = profit

	local qtyLabel = f:CreateFontString(nil, "OVERLAY", "GameFontNormalSmall")
	qtyLabel:SetPoint("TOPLEFT", f, "TOPLEFT", 18, -100)
	qtyLabel:SetText("Quantity:")
	f.qtyLabel = qtyLabel

	local qty = CreateFrame("EditBox", nil, f, "InputBoxTemplate")
	qty:SetSize(70, 20)
	qty:SetPoint("LEFT", qtyLabel, "RIGHT", 10, 0)
	qty:SetAutoFocus(false)
	qty:SetNumeric(true)
	qty:SetMaxLetters(6)
	qty:SetScript("OnEnterPressed", function(self)
		self:ClearFocus()
		local deal = Sniper.currentDeal
		if deal then
			Sniper:Buy(deal, tonumber(self:GetText()) or deal.quantity)
		end
	end)
	qty:SetScript("OnEscapePressed", function(self) self:ClearFocus() end)
	f.qty = qty

	local maxBtn = CreateFrame("Button", nil, f, "UIPanelButtonTemplate")
	maxBtn:SetSize(44, 20)
	maxBtn:SetPoint("LEFT", qty, "RIGHT", 6, 0)
	maxBtn:SetText("Max")
	maxBtn:SetScript("OnClick", function()
		local deal = Sniper.currentDeal
		if deal then
			qty:SetText(tostring(deal.quantity or 1))
			Sniper:Buy(deal, deal.quantity or 1)
		end
	end)
	f.maxBtn = maxBtn

	local status = f:CreateFontString(nil, "OVERLAY", "GameFontHighlightSmall")
	status:SetPoint("TOPLEFT", f, "TOPLEFT", 18, -126)
	status:SetWidth(320)
	status:SetJustifyH("LEFT")
	status:SetWordWrap(true)
	f.status = status

	local skip = CreateFrame("Button", nil, f, "UIPanelButtonTemplate")
	skip:SetSize(90, 24)
	skip:SetPoint("BOTTOMRIGHT", f, "BOTTOMRIGHT", -16, 16)
	skip:SetText("Skip")
	skip:SetScript("OnClick", function() Sniper:Skip() end)
	f.skip = skip

	local queueText = f:CreateFontString(nil, "OVERLAY", "GameFontDisableSmall")
	queueText:SetPoint("BOTTOM", f, "BOTTOM", 0, 44)
	f.queueText = queueText

	f:SetScript("OnHide", function()
		if FL.Secure and FL.Secure.Disarm and not InCombatLockdown() then
			FL.Secure.Disarm("buy")
		end
	end)

	popup = f
	Sniper.Popup = f
	AttachBuyButton()
	return f
end

-- Fill the popup with a deal and show it.
local function PopupShowDeal(deal)
	local f = CreatePopup()
	if not f then
		FL:Warn("Cannot open the sniper popup during combat; the deal is queued.")
		return false
	end
	Sniper.currentDeal = deal
	Sniper.lastDeal = deal
	local itemID = deal.itemID
	local _, _, _, _, icon = C_Item.GetItemInfoInstant(itemID)
	f.icon:SetTexture(icon or 134400)
	f.name:SetText(ItemLinkOrName(itemID))
	local pct = 0
	if deal.marketValue and deal.marketValue > 0 then
		pct = deal.unitPrice / deal.marketValue * 100
	end
	f.price:SetText(format("Unit %s  vs  market %s  (%.0f%%)", M(deal.unitPrice), M(deal.marketValue or 0), pct))
	local profitColor = (deal.profit or 0) >= 0 and "|cff40ff40" or "|cffff4040"
	f.profit:SetText(format("Profit %s%s|r for %d available · threshold %s", profitColor, M(deal.profit or 0, true), deal.quantity or 1, M(deal.threshold or 0)))
	f.qty:SetText(tostring(deal.requested or deal.quantity or 1))
	local queued = #Sniper.dealQueue
	f.queueText:SetText(queued > 0 and format("%d more deal%s queued", queued, queued == 1 and "" or "s") or "")
	if deal.statusText then
		PopupStatus(deal.statusText)
	else
		PopupStatus("Fetching current prices...")
	end
	if not InCombatLockdown() then
		AttachBuyButton()
	else
		popupNeedsAttach = true
	end
	f:Show()
	if FL.RequestItem then
		FL.RequestItem(itemID, function(loadedID)
			if Sniper.currentDeal == deal and f:IsShown() then
				f.name:SetText(ItemLinkOrName(loadedID))
			end
		end)
	end
	return true
end

-- Advance the popup to the next queued deal or hide it.
local function PopupNext()
	local queue = Sniper.dealQueue
	local nextDeal = tremove(queue, 1)
	if nextDeal then
		Sniper:ShowDeal(nextDeal)
	else
		Sniper.currentDeal = nil
		if popup then
			popup:Hide()
		end
	end
end

-- FL.Sniper:Skip() -- dismiss the current deal and show the next queued one
function Sniper:Skip()
	buyToken = buyToken + 1
	if FL.AuctionScan and FL.AuctionScan.CancelPurchase then
		pcall(FL.AuctionScan.CancelPurchase, FL.AuctionScan)
	end
	if FL.Secure and FL.Secure.Disarm and not InCombatLockdown() then
		FL.Secure.Disarm("buy")
	end
	PopupNext()
end

-- FL.Sniper:ShowDeal(deal) -- open the popup for a deal and pre-fetch its ladder
function Sniper:ShowDeal(deal)
	if type(deal) ~= "table" or not deal.itemID then
		return false
	end
	if not PopupShowDeal(deal) then
		tinsert(Sniper.dealQueue, 1, deal)
		return false
	end
	if FL.AuctionScan and FL.AuctionScan.isOpen then
		self:Buy(deal, deal.requested or deal.quantity or 1)
	else
		PopupStatus("Open the Auction House to buy this deal.", 1, 0.6, 0.2)
	end
	return true
end

-- FL.Sniper:ShowLastDeal() -- re-open the popup for the most recent deal
function Sniper:ShowLastDeal()
	if Sniper.lastDeal then
		return self:ShowDeal(Sniper.lastDeal)
	end
	FL:Print("No sniper deal recorded yet.")
	return false
end

-- Queue a deal: show immediately when the popup is idle, otherwise append.
local function EnqueueDeal(deal)
	if Sniper.currentDeal and popup and popup:IsShown() then
		tinsert(Sniper.dealQueue, deal)
		if popup.queueText then
			local queued = #Sniper.dealQueue
			popup.queueText:SetText(format("%d more deal%s queued", queued, queued == 1 and "" or "s"))
		end
	else
		Sniper:ShowDeal(deal)
	end
end

-------------------------------------------------------------------------------
-- §6.4 FL.Sniper — evaluation
-------------------------------------------------------------------------------
local browseSorts = { { sortOrder = 0, reverseSort = false } }
local browseClassFilter = { { classID = 0 } }
local browseQuery = { searchString = "", sorts = browseSorts, filters = {}, itemClassFilters = nil, minLevel = 0, maxLevel = 0 }
local sniperLogScratch = {}
local sniperLogTrim = {}
local ladderOrder = {}
local ladderPrices

-- Age in seconds of a results timestamp (accepts time() or GetTime() stamps).
local function AgeOf(ts)
	if type(ts) ~= "number" then
		return huge
	end
	if ts > 1000000000 then
		return time() - ts
	end
	return GetTime() - ts
end

-- Commodity flag for a browse result (item key info → market table → stack size).
local function IsCommodityKey(itemKey, itemID, totalQuantity)
	if C_AuctionHouse and C_AuctionHouse.GetItemKeyInfo and itemKey then
		local ok, info = pcall(C_AuctionHouse.GetItemKeyInfo, itemKey)
		if ok and info and info.isCommodity ~= nil then
			return info.isCommodity and true or false
		end
	end
	if FL.Market and FL.Market.Get then
		local flag = FL.Market.Get(itemID, "isCommodity", itemKey and itemKey.itemSuffix or 0)
		if flag ~= nil then
			return flag and true or false
		end
	end
	local stack = select(8, C_Item.GetItemInfo(itemID))
	if stack then
		return stack > 1
	end
	return (totalQuantity or 0) > 1
end

-- Sort ladder indices ascending by unit price.
local function LadderLess(a, b)
	local pa, pb = ladderPrices[a], ladderPrices[b]
	if pa == pb then
		return a < b
	end
	return pa < pb
end

-- Mark the sniper log row that produced a deal as bought.
local function MarkDealBought(deal)
	local db = FL.DB and FL.DB.sniperLog
	if not db then
		return
	end
	db:FindAll("itemID", deal.itemID, sniperLogScratch)
	for i = 1, sniperLogScratch.n or #sniperLogScratch do
		local rid = sniperLogScratch[i]
		if db:Get(rid, "ts") == deal.ts and db:Get(rid, "unitPrice") == deal.unitPrice then
			db:Set(rid, "bought", true)
			return
		end
	end
end

-- Keep the sniper log bounded (oldest rows first).
local function TrimSniperLog(maxRows)
	local db = FL.DB and FL.DB.sniperLog
	if not db then
		return
	end
	local excess = db:Count() - maxRows
	if excess <= 0 then
		return
	end
	wipe(sniperLogTrim)
	local q = db:NewQuery():OrderBy("ts", false):Limit(excess):Execute()
	local n = 0
	for i = 1, q.n do
		n = n + 1
		sniperLogTrim[n] = q.results[i]
	end
	q:Release()
	DeleteRows(db, sniperLogTrim, n)
end

-- Sound / raid warning / chat alert for a deal.
local function AlertDeal(deal)
	local sn = SS("sniper")
	local link = ItemLinkOrName(deal.itemID)
	if sn.sound ~= false and PlaySound then
		pcall(PlaySound, (SOUNDKIT and SOUNDKIT.RAID_WARNING) or SOUND_RAID_WARNING, "Master")
	end
	if sn.raidWarning ~= false and RaidNotice_AddMessage and RaidWarningFrame and ChatTypeInfo then
		pcall(RaidNotice_AddMessage, RaidWarningFrame, format("Snipe: %s @ %s", ItemName(deal.itemID), M(deal.unitPrice, true)), ChatTypeInfo["RAID_WARNING"])
	end
	FL:Print("Deal: %s x%d @ %s (market %s, profit %s)", link, deal.quantity, M(deal.unitPrice), M(deal.marketValue), M(deal.profit))
end

-- Evaluate one BrowseResultInfo against the sniper formula.
local function EvaluateBrowseResult(r)
	local key = r and r.itemKey
	local itemID = key and key.itemID
	if not itemID then
		return
	end
	if evaluatedInPass[itemID] == passToken then
		return
	end
	evaluatedInPass[itemID] = passToken
	local minPrice = tonumber(r.minPrice) or 0
	if minPrice <= 0 then
		return
	end
	local sn = SS("sniper")
	if r.containsOwnerItem and sn.ignoreOwn ~= false then
		return
	end
	local suffix = key.itemSuffix or 0
	local threshold = Eval(sn.formula or "max(vendorsell, 35% dbmarket)", itemID, suffix)
	if not threshold or threshold <= 0 or minPrice >= threshold then
		return
	end
	local marketValue = (FL.Market and FL.Market.MarketValue(itemID)) or 0
	if marketValue <= 0 and FL.Market and FL.Market.Historical then
		marketValue = FL.Market.Historical(itemID) or 0
	end
	if marketValue <= 0 then
		marketValue = threshold
	end
	local isCommodity = IsCommodityKey(key, itemID, r.totalQuantity)
	local maxDeal = Money(sn.maxPricePerDeal, 5000000)
	local qty = 1
	if isCommodity then
		qty = tonumber(r.totalQuantity) or 1
		if maxDeal > 0 then
			qty = mmin(qty, floor(maxDeal / minPrice))
		end
		if qty < 1 then
			return
		end
	elseif maxDeal > 0 and minPrice > maxDeal then
		return
	end
	local profit = (marketValue - minPrice) * qty
	if profit < Money(sn.minProfit, 5000) then
		return
	end
	local dedupeKey = itemID .. ":" .. minPrice
	local now = GetTime()
	local seenAt = Sniper.seen[dedupeKey]
	if seenAt and now - seenAt < SNIPER_SEEN_WINDOW then
		return
	end
	Sniper.seen[dedupeKey] = now
	local ts = time()
	local deal = {
		itemID = itemID,
		suffix = suffix,
		unitPrice = minPrice,
		quantity = qty,
		requested = qty,
		marketValue = marketValue,
		threshold = threshold,
		isCommodity = isCommodity,
		itemKey = { itemID = itemID, itemLevel = key.itemLevel or 0, itemSuffix = suffix, battlePetSpeciesID = key.battlePetSpeciesID or 0 },
		profit = profit,
		ts = ts,
		score = Intel.DealScore(itemID),
	}
	local db = FL.DB and FL.DB.sniperLog
	if db then
		db:Insert({
			ts = ts,
			itemID = itemID,
			unitPrice = minPrice,
			quantity = qty,
			marketValue = marketValue,
			reason = format("%.0f%% of market", minPrice / marketValue * 100),
			bought = false,
		})
	end
	Sniper.stats.deals = Sniper.stats.deals + 1
	FL.Fire("FL_SNIPE_FOUND", deal)
	AlertDeal(deal)
	EnqueueDeal(deal)
end

-- Handle one page of browse results.
local function OnBrowsePage(results)
	if type(results) ~= "table" then
		return
	end
	for i = 1, #results do
		local ok, err = pcall(EvaluateBrowseResult, results[i])
		if not ok then
			FL:Debug("Sniper evaluate error: %s", tostring(err))
		end
	end
end

-- Schedule the next sniper pass.
local function ScheduleNextPass()
	if not sniperRunning then
		return
	end
	local interval = tonumber(SS("sniper").intervalSec) or 2
	if interval < 0.5 then
		interval = 0.5
	end
	After(interval, function() Sniper:Tick() end)
end

-- Finish the current pass and schedule the next one.
local function FinishPass()
	if not sniperInPass then
		return
	end
	sniperInPass = false
	Sniper.stats.passes = Sniper.stats.passes + 1
	Sniper.stats.lastPassAt = time()
	local now = GetTime()
	for key, ts in pairs(Sniper.seen) do
		if now - ts > SNIPER_SEEN_WINDOW then
			Sniper.seen[key] = nil
		end
	end
	if Sniper.stats.passes % 20 == 0 then
		TrimSniperLog(500)
	end
	FL.Fire("FL_SNIPER_PASS", Sniper.stats.passes)
	ScheduleNextPass()
end

-- FL.Sniper:Tick() -- run one browse pass (never overlapping)
function Sniper:Tick()
	if not sniperRunning or sniperInPass then
		return
	end
	local scan = FL.AuctionScan
	if not (scan and scan.isOpen) then
		self:Stop()
		return
	end
	if scan.state == "full" or not scan.RunBrowseScan then
		ScheduleNextPass()
		return
	end
	sniperInPass = true
	passToken = passToken + 1
	local token = passToken
	local sn = SS("sniper")
	local priceOrder = (Enum and Enum.AuctionHouseSortOrder and Enum.AuctionHouseSortOrder.Price) or 0
	browseSorts[1].sortOrder = priceOrder
	browseSorts[1].reverseSort = false
	if sn.classRotation ~= false and #Sniper.classRotation > 0 then
		rotationIndex = rotationIndex % #Sniper.classRotation + 1
		browseClassFilter[1].classID = Sniper.classRotation[rotationIndex]
		browseQuery.itemClassFilters = browseClassFilter
	else
		browseQuery.itemClassFilters = nil
	end
	browseQuery.searchString = ""
	browseQuery.minLevel = 0
	browseQuery.maxLevel = 0
	local ok, result = pcall(scan.RunBrowseScan, scan, browseQuery,
		function(results)
			if token == passToken then
				OnBrowsePage(results)
			end
		end,
		function()
			if token == passToken then
				FinishPass()
			end
		end)
	if not ok then
		FL:Debug("Sniper browse failed: %s", tostring(result))
		FinishPass()
		return
	end
	if result == false then
		FinishPass()
		return
	end
	After(SNIPER_PASS_TIMEOUT, function()
		if token == passToken and sniperInPass then
			FinishPass()
		end
	end)
end

-- Start the loop (AH must be open).
function Sniper:Start()
	if sniperRunning then
		return true
	end
	if not (FL.AuctionScan and FL.AuctionScan.isOpen) then
		return false
	end
	sniperRunning = true
	sniperInPass = false
	rotationIndex = 0
	FL:Print("Sniper started (every %.1fs, formula: %s).", tonumber(SS("sniper").intervalSec) or 2, tostring(SS("sniper").formula))
	FL.Fire("FL_SNIPER_STATE", true)
	self:Tick()
	return true
end

-- Stop the loop and invalidate in-flight callbacks.
function Sniper:Stop()
	if not sniperRunning then
		return
	end
	sniperRunning = false
	sniperInPass = false
	passToken = passToken + 1
	FL:Print("Sniper stopped after %d passes, %d deals, %d bought.", Sniper.stats.passes, Sniper.stats.deals, Sniper.stats.bought)
	FL.Fire("FL_SNIPER_STATE", false)
end

-- FL.Sniper:SetEnabled(bool) -- persist the setting and start/stop when the AH is open
function Sniper:SetEnabled(enabled)
	enabled = enabled and true or false
	local sn = SS("sniper")
	if sn ~= EMPTY then
		sn.enabled = enabled
	end
	FL.Fire("FL_SETTINGS_CHANGED", "sniper.enabled", enabled)
	if enabled then
		if not self:Start() then
			FL:Print("Sniper enabled; it starts automatically when the Auction House is open.")
		end
	else
		self:Stop()
	end
	return sniperRunning
end

-- FL.Sniper:IsRunning() -> boolean
function Sniper:IsRunning()
	return sniperRunning
end

-------------------------------------------------------------------------------
-- §6.4 FL.Sniper — buying
-------------------------------------------------------------------------------
-- Common completion handler for both purchase paths.
local function OnDealPurchaseDone(deal, qty, ok, reason, unitPrice)
	if ok then
		Sniper.stats.bought = Sniper.stats.bought + 1
		deal.bought = true
		MarkDealBought(deal)
		deal.statusText = format("Bought %d x %s.", qty, ItemName(deal.itemID))
		PopupStatus(deal.statusText, 0.3, 1, 0.3)
		FL:Print("Bought %d x %s for %s.", qty, ItemLinkOrName(deal.itemID), M((unitPrice or deal.unitPrice) * qty))
		FL.Fire("FL_SNIPE_BOUGHT", deal, qty)
		After(1.0, function()
			if Sniper.currentDeal == deal then
				PopupNext()
			end
		end)
	else
		local text = tostring(reason or "failed")
		if reason == "price_changed" and unitPrice then
			text = format("price changed to %s", M(unitPrice))
		end
		deal.statusText = "Purchase failed: " .. text
		PopupStatus(deal.statusText, 1, 0.4, 0.4)
		FL:Warn("Purchase of %s failed: %s", ItemLinkOrName(deal.itemID), text)
	end
end

-- Commodity path: count what is available at or below the deal price, then arm the buy.
local function BuyCommodityDeal(deal, results)
	local n = results and results.n or 0
	local prices, qtys, own = results and results.unitPrices, results and results.quantities, results and results.own
	if n <= 0 or not prices or not qtys then
		deal.statusText = "Deal gone: no auctions found."
		PopupStatus(deal.statusText, 1, 0.6, 0.2)
		return false
	end
	wipe(ladderOrder)
	for i = 1, n do
		ladderOrder[i] = i
	end
	ladderPrices = prices
	tsort(ladderOrder, LadderLess)
	local ignoreOwn = SS("sniper").ignoreOwn ~= false
	local available = 0
	for k = 1, n do
		local i = ladderOrder[k]
		if prices[i] > deal.unitPrice then
			break
		end
		if not (ignoreOwn and own and own[i]) then
			available = available + (qtys[i] or 0)
		end
	end
	if available <= 0 then
		deal.statusText = format("Deal gone: nothing left at or below %s.", M(deal.unitPrice, true))
		PopupStatus(deal.statusText, 1, 0.6, 0.2)
		FL:Print("%s: nothing left at %s.", ItemLinkOrName(deal.itemID), M(deal.unitPrice))
		return false
	end
	local qty = mmin(deal.requested or deal.quantity or 1, available)
	deal.quantity = available
	deal.statusText = format("%d available at or below %s. Click BUY, then CONFIRM.", available, M(deal.unitPrice, true))
	PopupStatus(deal.statusText, 0.6, 1, 0.6)
	if popup and popup.qty then
		popup.qty:SetText(tostring(qty))
	end
	FL.AuctionScan:BeginCommodityPurchase(deal.itemID, qty, deal.unitPrice, function(ok, reason, unit)
		OnDealPurchaseDone(deal, qty, ok, reason, unit)
	end)
	return true
end

-- Item path: locate the auction with the matching buyout and arm the buy.
local function BuyItemDeal(deal, results)
	local n = results and results.n or 0
	local prices, ids, own = results and results.unitPrices, results and results.auctionIDs, results and results.own
	if n <= 0 or not prices or not ids then
		deal.statusText = "Deal gone: no auctions found."
		PopupStatus(deal.statusText, 1, 0.6, 0.2)
		return false
	end
	local ignoreOwn = SS("sniper").ignoreOwn ~= false
	local bestIndex, bestPrice
	for i = 1, n do
		local price = prices[i]
		if price and price > 0 and price <= deal.unitPrice and ids[i] and ids[i] ~= 0 and not (ignoreOwn and own and own[i]) then
			if not bestPrice or price < bestPrice then
				bestPrice, bestIndex = price, i
			end
		end
	end
	if not bestIndex then
		deal.statusText = format("Deal gone: no auction at or below %s.", M(deal.unitPrice, true))
		PopupStatus(deal.statusText, 1, 0.6, 0.2)
		FL:Print("%s: auction at %s is gone.", ItemLinkOrName(deal.itemID), M(deal.unitPrice))
		return false
	end
	deal.statusText = format("Auction found at %s. Click BUY to buy it out.", M(bestPrice, true))
	PopupStatus(deal.statusText, 0.6, 1, 0.6)
	if popup and popup.qty then
		popup.qty:SetText("1")
	end
	FL.AuctionScan:BeginItemBuyout(ids[bestIndex], bestPrice, deal.itemID, function(ok, reason)
		OnDealPurchaseDone(deal, 1, ok, reason, bestPrice)
	end)
	return true
end

-- FL.Sniper:Buy(deal, quantity) -- fetch the exact ladder and arm the secure buy button
function Sniper:Buy(deal, quantity)
	if type(deal) ~= "table" or not deal.itemID then
		return false
	end
	local scan = FL.AuctionScan
	if not (scan and scan.isOpen) then
		FL:Warn("Open the Auction House before buying.")
		return false
	end
	quantity = floor(tonumber(quantity) or deal.quantity or 1)
	if quantity < 1 then
		quantity = 1
	end
	deal.requested = quantity
	if Sniper.currentDeal ~= deal or not (popup and popup:IsShown()) then
		if not PopupShowDeal(deal) then
			return false
		end
	end
	deal.statusText = nil
	PopupStatus("Fetching current prices...")
	buyToken = buyToken + 1
	local token = buyToken
	deal.buyToken = token
	local function proceed(results)
		if token ~= buyToken or Sniper.currentDeal ~= deal then
			return
		end
		if not results and scan.GetLastResults then
			results = scan.GetLastResults(deal.itemID)
		end
		if deal.isCommodity then
			BuyCommodityDeal(deal, results)
		else
			BuyItemDeal(deal, results)
		end
	end
	local last = scan.GetLastResults and scan.GetLastResults(deal.itemID)
	if last and last.n and last.n > 0 and AgeOf(last.ts) < LADDER_FRESH_SEC then
		proceed(last)
		return true
	end
	local ok, err
	if deal.isCommodity then
		ok, err = pcall(scan.ScanItem, scan, deal.itemID, function(_, results) proceed(results) end)
	else
		ok, err = pcall(scan.RunItemScan, scan, deal.itemID, function(_, results) proceed(results) end)
	end
	if not ok then
		FL:Warn("Could not query %s: %s", ItemLinkOrName(deal.itemID), tostring(err))
		PopupStatus("Query failed; try again.", 1, 0.4, 0.4)
		return false
	end
	return true
end

-------------------------------------------------------------------------------
-- §6.5 FL.Posting — state and pools
-------------------------------------------------------------------------------
Posting.queue = Posting.queue or {}
Posting.index = 0
Posting.currentMin = Posting.currentMin or {}
Posting.lastPost = nil
Posting.armedEntry = nil

local entryPool = {}
local slotPool = {}
local queueByItem = {}
local pricingToken = 0
local pricingActive = false
local cancelToken = 0

-- Take a bag-slot record from the pool.
local function AcquireSlot(bag, slot, count)
	local s = tremove(slotPool) or {}
	s.bag, s.slot, s.count = bag, slot, count
	return s
end

-- Take a queue entry from the pool, reset to defaults.
local function AcquireEntry(itemID)
	local e = tremove(entryPool) or { bagSlots = {} }
	e.itemID = itemID
	e.name = ItemName(itemID)
	e.isCommodity = nil
	e.total = 0
	e.price = nil
	e.minPrice = nil
	e.maxPrice = nil
	e.competitorMin = nil
	e.deposit = 0
	e.postedCount = 0
	e.postedAuctions = 0
	e.slotIndex = 1
	e.status = "pending"
	e.reason = ""
	e.scanned = false
	e.quality = nil
	e.sellPrice = 0
	return e
end

-- Return an entry and its slot records to the pools.
local function ReleaseEntry(e)
	local slots = e.bagSlots
	for i = #slots, 1, -1 do
		slotPool[#slotPool + 1] = slots[i]
		slots[i] = nil
	end
	entryPool[#entryPool + 1] = e
end

-- Round a unit price UP to whole silver when the server rejects copper values.
local function RoundUpUnitPrice(price)
	price = ceil(price)
	if C_AuctionHouse and C_AuctionHouse.SupportsCopperValues then
		local ok, supports = pcall(C_AuctionHouse.SupportsCopperValues)
		if ok and supports then
			return mmax(price, 1)
		end
	end
	return mmax(ceil(price / 100) * 100, 100)
end

-- Commodity status for a bag slot (true/false, or nil when unknown).
local function SlotCommodityStatus(bag, slot)
	if not (C_AuctionHouse and C_AuctionHouse.GetItemCommodityStatus and ItemLocation and ItemLocation.CreateFromBagAndSlot) then
		return nil
	end
	local ok, status = pcall(function()
		return C_AuctionHouse.GetItemCommodityStatus(ItemLocation:CreateFromBagAndSlot(bag, slot))
	end)
	if not ok then
		return nil
	end
	local commodity = (Enum and Enum.ItemCommodityStatus and Enum.ItemCommodityStatus.Commodity) or 2
	local item = (Enum and Enum.ItemCommodityStatus and Enum.ItemCommodityStatus.Item) or 1
	if status == commodity then
		return true
	elseif status == item then
		return false
	end
	return nil
end

-- Sort queue entries alphabetically, then by itemID.
local function EntryLess(a, b)
	if a.name == b.name then
		return a.itemID < b.itemID
	end
	return a.name < b.name
end

-- FL.Posting:BuildQueue() -> queueArray -- scan bags 0..4 and group sellable items
function Posting:BuildQueue()
	local queue = Posting.queue
	for i = #queue, 1, -1 do
		ReleaseEntry(queue[i])
		queue[i] = nil
	end
	wipe(queueByItem)
	wipe(Posting.currentMin)
	Posting.index = 0
	Posting.armedEntry = nil
	local ps = SS("posting")
	local ignoreSoulbound = ps.ignoreSoulbound ~= false
	local groups = FL.DB and FL.DB.groups
	local ahOpen = FL.AuctionScan and FL.AuctionScan.isOpen
	if not (C_Container and C_Container.GetContainerNumSlots and C_Container.GetContainerItemInfo) then
		return queue
	end
	for bag = BAG_FIRST, BAG_LAST do
		local slots = C_Container.GetContainerNumSlots(bag) or 0
		for slot = 1, slots do
			local info = C_Container.GetContainerItemInfo(bag, slot)
			local itemID = info and info.itemID
			if itemID and not info.isLocked then
				local skip = false
				if ignoreSoulbound and info.isBound then
					skip = true
				end
				local classID, quality, sell
				if not skip then
					local _, _, _, _, _, cid = C_Item.GetItemInfoInstant(itemID)
					classID = cid
					if classID == CLASS_QUEST then
						skip = true
					end
				end
				if not skip then
					quality = info.quality or (FL.GetItemQuality and FL.GetItemQuality(itemID)) or 1
					sell = (FL.GetItemSellPrice and FL.GetItemSellPrice(itemID)) or 0
					if quality == 0 and sell == 0 and not (groups and groups:FindFirst("itemID", itemID)) then
						skip = true
					end
				end
				if not skip and ahOpen and C_AuctionHouse and C_AuctionHouse.IsSellItemValid and ItemLocation then
					local ok, valid = pcall(function()
						return C_AuctionHouse.IsSellItemValid(ItemLocation:CreateFromBagAndSlot(bag, slot), false)
					end)
					if ok and valid == false then
						skip = true
					end
				end
				if not skip then
					local entry = queueByItem[itemID]
					if not entry then
						entry = AcquireEntry(itemID)
						entry.quality = quality
						entry.sellPrice = sell
						queueByItem[itemID] = entry
						queue[#queue + 1] = entry
					end
					local count = info.stackCount or 1
					entry.bagSlots[#entry.bagSlots + 1] = AcquireSlot(bag, slot, count)
					entry.total = entry.total + count
					if entry.isCommodity == nil then
						entry.isCommodity = SlotCommodityStatus(bag, slot)
					end
				end
			end
		end
	end
	for i = 1, #queue do
		local entry = queue[i]
		if entry.isCommodity == nil then
			local stack = select(8, C_Item.GetItemInfo(entry.itemID))
			if stack then
				entry.isCommodity = stack > 1
			else
				local biggest = 0
				for k = 1, #entry.bagSlots do
					biggest = mmax(biggest, entry.bagSlots[k].count)
				end
				entry.isCommodity = biggest > 1
			end
		end
		if entry.name == "" or strfind(entry.name, "^item:") then
			FL.RequestItem(entry.itemID, function(loadedID)
				if queueByItem[loadedID] == entry then
					entry.name = ItemName(loadedID)
				end
			end)
		end
	end
	tsort(queue, EntryLess)
	FL.Fire("FL_POSTING_QUEUE", #queue)
	return queue
end

-------------------------------------------------------------------------------
-- §6.5 FL.Posting — pricing
-------------------------------------------------------------------------------
-- Lowest unit price in a ladder that is not our own auction (nil when none).
local function CompetitorMin(results)
	local n = results and results.n or 0
	if n <= 0 then
		return nil
	end
	local prices, own = results.unitPrices, results.own
	local best
	for i = 1, n do
		local price = prices[i]
		if price and price > 0 and not (own and own[i]) then
			if not best or price < best then
				best = price
			end
		end
	end
	return best
end

-- Price one queue entry from scan results and the posting formulas.
local function PriceEntry(entry, results)
	local itemID = entry.itemID
	local competitorMin = CompetitorMin(results)
	entry.scanned = results ~= nil
	entry.competitorMin = competitorMin
	Posting.currentMin[itemID] = competitorMin
	if FL.Parser and FL.Parser.ClearCache and FL.Parser.memo then
		wipe(FL.Parser.memo)
	end
	local ps = SS("posting")
	local price = Eval(ps.priceFormula, itemID)
	local minP = Eval(ps.minFormula, itemID)
	local maxP = Eval(ps.maxFormula, itemID)
	entry.minPrice = minP
	entry.maxPrice = maxP
	entry.price = nil
	if not price or price <= 0 then
		entry.status, entry.reason = "skip", "no price"
		return
	end
	if minP and minP > 0 and price < minP then
		if ps.skipIfBelowMin ~= false then
			entry.status, entry.reason = "skip", "below min"
			return
		end
		price = minP
	end
	if maxP and maxP > 0 and price > maxP then
		price = maxP
	end
	if competitorMin and minP and minP > 0 and competitorMin <= minP then
		entry.status, entry.reason = "skip", "market below minimum"
		return
	end
	local owned = FL.AuctionScan and FL.AuctionScan.ownedByItem and FL.AuctionScan.ownedByItem[itemID]
	if owned and (owned.count or 0) > 0 then
		if not competitorMin or (owned.minBuyoutUnit and owned.minBuyoutUnit <= competitorMin) then
			entry.status, entry.reason = "skip", "already lowest"
			return
		end
	end
	price = RoundUnitPrice(price)
	if minP and minP > 0 and price < minP then
		if ps.skipIfBelowMin ~= false then
			entry.status, entry.reason = "skip", "below min"
			return
		end
		price = RoundUpUnitPrice(minP)
	end
	if price < 1 then
		entry.status, entry.reason = "skip", "no price"
		return
	end
	entry.price = price
	entry.status, entry.reason = "priced", ""
end

-- FL.Posting:PriceQueue(onProgress) -- scan each queue item and compute post prices
function Posting:PriceQueue(onProgress)
	local queue = Posting.queue
	local scan = FL.AuctionScan
	if #queue == 0 then
		FL:Print("Posting queue is empty; scan your bags first.")
		return false
	end
	if not (scan and scan.isOpen and scan.ScanItem) then
		FL:Warn("Open the Auction House before pricing.")
		return false
	end
	pricingToken = pricingToken + 1
	local token = pricingToken
	pricingActive = true
	local total = #queue
	local i = 0
	local step
	step = function()
		if token ~= pricingToken then
			return
		end
		local entry
		while i < total do
			i = i + 1
			local candidate = queue[i]
			if candidate and candidate.status ~= "posted" then
				entry = candidate
				break
			end
		end
		if not entry then
			pricingActive = false
			local ready, skipped = 0, 0
			for k = 1, #queue do
				if queue[k].status == "priced" then
					ready = ready + 1
				elseif queue[k].status == "skip" or queue[k].status == "error" then
					skipped = skipped + 1
				end
			end
			if onProgress then
				pcall(onProgress, total, total, nil)
			end
			FL.Fire("FL_POSTING_PRICED", ready, skipped)
			FL:Print("Priced %d items: %d ready to post, %d skipped.", total, ready, skipped)
			return
		end
		entry.status, entry.reason = "pricing", ""
		local done = false
		local function finish(results)
			if done or token ~= pricingToken then
				return
			end
			done = true
			if not results and scan.GetLastResults then
				local last = scan.GetLastResults(entry.itemID)
				if last and AgeOf(last.ts) < PRICE_SCAN_TIMEOUT * 2 then
					results = last
				end
			end
			local ok, err = pcall(PriceEntry, entry, results)
			if not ok then
				entry.status, entry.reason = "error", tostring(err)
			end
			if onProgress then
				pcall(onProgress, i, total, entry)
			end
			step()
		end
		local ok, err = pcall(scan.ScanItem, scan, entry.itemID, function(_, results) finish(results) end)
		if not ok then
			entry.status, entry.reason = "error", tostring(err)
			done = true
			step()
			return
		end
		After(PRICE_SCAN_TIMEOUT, function()
			if not done then
				finish(nil)
			end
		end)
	end
	step()
	return true
end

-------------------------------------------------------------------------------
-- §6.5 FL.Posting — posting
-------------------------------------------------------------------------------
-- First recorded bag slot that still holds the entry's item (rescans bags when all moved).
local function FindSlotFor(entry, fromIndex)
	local slots = entry.bagSlots
	for k = fromIndex or 1, #slots do
		local s = slots[k]
		local info = C_Container.GetContainerItemInfo(s.bag, s.slot)
		if info and info.itemID == entry.itemID and not info.isLocked then
			return s.bag, s.slot, k
		end
	end
	for bag = BAG_FIRST, BAG_LAST do
		local n = C_Container.GetContainerNumSlots(bag) or 0
		for slot = 1, n do
			local info = C_Container.GetContainerItemInfo(bag, slot)
			if info and info.itemID == entry.itemID and not info.isLocked then
				return bag, slot, nil
			end
		end
	end
	return nil
end

-- Next postable entry after Posting.index (wrapping once).
local function NextPricedEntry()
	local queue = Posting.queue
	local n = #queue
	for i = Posting.index + 1, n do
		if queue[i].status == "priced" then
			return queue[i], i
		end
	end
	for i = 1, mmin(Posting.index, n) do
		if queue[i].status == "priced" then
			return queue[i], i
		end
	end
	return nil
end

-- FL.Posting:PostNext() -- arm the secure post button for the next priced entry
function Posting:PostNext()
	if InCombatLockdown() then
		FL:Warn("Cannot arm the post button in combat.")
		return false
	end
	if not (FL.AuctionScan and FL.AuctionScan.isOpen) then
		FL:Warn("Open the Auction House before posting.")
		return false
	end
	if not (FL.Secure and FL.Secure.Arm) then
		return false
	end
	local ps = SS("posting")
	local duration = floor(tonumber(ps.duration) or 2)
	if duration < 1 then
		duration = 1
	elseif duration > 3 then
		duration = 3
	end
	local keep = floor(tonumber(ps.keepQuantity) or 0)
	local stackSize = floor(tonumber(ps.stackSizeCommodity) or 0)
	local entry, idx, qty, bag, slot
	while true do
		entry, idx = NextPricedEntry()
		if not entry then
			FL.Secure.Disarm("post")
			Posting.armedEntry = nil
			FL:Print("Nothing left to post.")
			FL.Fire("FL_POSTING_DONE")
			return false
		end
		Posting.index = idx
		if entry.isCommodity then
			local avail = entry.total - entry.postedCount - keep
			if avail <= 0 then
				entry.status, entry.reason = "skip", "keep quantity"
			else
				qty = (stackSize > 0) and mmin(stackSize, avail) or avail
				bag, slot = FindSlotFor(entry, 1)
				if not bag then
					entry.status, entry.reason = "error", "item moved"
				end
			end
		else
			qty = 1
			local k
			bag, slot, k = FindSlotFor(entry, entry.slotIndex)
			if not bag then
				entry.status, entry.reason = "error", "item moved"
			elseif k then
				entry.slotIndex = k
			end
		end
		if entry.status == "priced" and bag then
			break
		end
	end
	local itemID, unit = entry.itemID, entry.price
	local deposit = 0
	if entry.isCommodity then
		if C_AuctionHouse.CalculateCommodityDeposit then
			local ok, value = pcall(C_AuctionHouse.CalculateCommodityDeposit, itemID, duration, qty)
			if ok and type(value) == "number" then
				deposit = value
			end
		end
	elseif C_AuctionHouse.CalculateItemDeposit and ItemLocation then
		local ok, value = pcall(function()
			return C_AuctionHouse.CalculateItemDeposit(ItemLocation:CreateFromBagAndSlot(bag, slot), duration, qty)
		end)
		if ok and type(value) == "number" then
			deposit = value
		end
	end
	entry.deposit = deposit
	local postBag, postSlot, postQty, postDuration = bag, slot, qty, duration
	local armed = FL.Secure.Arm("post", {
		label = format("POST %dx %s @ %s", postQty, entry.name, M(unit, true)),
		fn = function()
			local loc = ItemLocation:CreateFromBagAndSlot(postBag, postSlot)
			if C_AuctionHouse.IsSellItemValid and not C_AuctionHouse.IsSellItemValid(loc, true) then
				error("item is not valid for sale")
			end
			Posting.lastPost = { itemID = itemID, quantity = postQty, unitPrice = unit, deposit = deposit, entry = entry, index = idx, ts = time(), ledgered = false }
			entry.status = "posting"
			if entry.isCommodity then
				local needs = C_AuctionHouse.PostCommodity(loc, postDuration, postQty, unit)
				if needs and C_AuctionHouse.ConfirmPostCommodity then
					C_AuctionHouse.ConfirmPostCommodity(loc, postDuration, postQty, unit)
				end
			else
				local needs = C_AuctionHouse.PostItem(loc, postDuration, 1, unit, unit)
				if needs and C_AuctionHouse.ConfirmPostItem then
					C_AuctionHouse.ConfirmPostItem(loc, postDuration, 1, unit, unit)
				end
			end
		end,
		onFail = function(err)
			entry.status, entry.reason = "error", tostring(err)
			FL:Warn("Posting %s failed: %s", entry.name, tostring(err))
			After(0.3, function() Posting:PostNext() end)
		end,
	})
	if armed == false then
		return false
	end
	Posting.armedEntry = entry
	FL.Fire("FL_POSTING_ARMED", entry, postQty, unit)
	return true
end

-- AUCTION_HOUSE_AUCTION_CREATED → mark the entry, advance and re-arm.
local function OnAuctionCreatedPosting()
	local last = Posting.lastPost
	local entry = last and last.entry
	if entry and entry.status == "posting" then
		entry.postedCount = entry.postedCount + (last.quantity or 0)
		entry.postedAuctions = entry.postedAuctions + 1
		local ps = SS("posting")
		if entry.isCommodity then
			local keep = floor(tonumber(ps.keepQuantity) or 0)
			local stackSize = floor(tonumber(ps.stackSizeCommodity) or 0)
			local remaining = entry.total - entry.postedCount - keep
			if remaining > 0 and stackSize > 0 then
				entry.status, entry.reason = "priced", ""
			else
				entry.status, entry.reason = "posted", ""
			end
		else
			entry.slotIndex = entry.slotIndex + 1
			if entry.slotIndex > #entry.bagSlots then
				entry.status, entry.reason = "posted", ""
			else
				entry.status, entry.reason = "priced", ""
			end
		end
		if entry.status == "priced" and last.index then
			Posting.index = last.index - 1
		end
		FL.Fire("FL_POSTING_POSTED", entry, last.quantity, last.unitPrice)
	end
	if FL.AuctionScan and FL.AuctionScan.isOpen and not InCombatLockdown() then
		After(0.2, function()
			if FL.AuctionScan.isOpen then
				Posting:PostNext()
			end
		end)
	end
end

-- AUCTION_HOUSE_POST_ERROR → mark the entry and move on.
local function OnPostError()
	local last = Posting.lastPost
	local entry = last and last.entry
	if entry and entry.status == "posting" then
		entry.status, entry.reason = "error", "post error"
		FL:Warn("The Auction House rejected the post for %s.", entry.name)
	end
	if FL.Secure and FL.Secure.Disarm and not InCombatLockdown() then
		FL.Secure.Disarm("post")
	end
	if FL.AuctionScan and FL.AuctionScan.isOpen and not InCombatLockdown() then
		After(0.5, function() Posting:PostNext() end)
	end
end

-------------------------------------------------------------------------------
-- §6.5 FL.Posting — cancel undercut auctions
-------------------------------------------------------------------------------
-- FL.Posting:CancelUndercut(onDone) -- find own auctions above the competitor min and arm cancels
function Posting:CancelUndercut(onDone)
	local scan = FL.AuctionScan
	if not (scan and scan.isOpen and scan.QueryOwned and scan.ScanItem) then
		FL:Warn("Open the Auction House before cancelling undercut auctions.")
		return false
	end
	if InCombatLockdown() then
		FL:Warn("Cannot cancel auctions in combat.")
		return false
	end
	cancelToken = cancelToken + 1
	local token = cancelToken
	scan:QueryOwned(function(owned)
		if token ~= cancelToken then
			return
		end
		local byItem, items, nItems = {}, {}, 0
		if type(owned) == "table" then
			for i = 1, #owned do
				local a = owned[i]
				local itemID = a and a.itemKey and a.itemKey.itemID
				local buyout = a and tonumber(a.buyoutAmount) or 0
				if itemID and buyout > 0 and (a.status == nil or a.status == STATUS_ACTIVE) and a.auctionID then
					local list = byItem[itemID]
					if not list then
						list = {}
						byItem[itemID] = list
						nItems = nItems + 1
						items[nItems] = itemID
					end
					local qty = tonumber(a.quantity) or 1
					if qty < 1 then
						qty = 1
					end
					list[#list + 1] = { auctionID = a.auctionID, unit = floor(buyout / qty), itemID = itemID }
				end
			end
		end
		if nItems == 0 then
			FL:Print("No active auctions to check.")
			if onDone then
				pcall(onDone, 0, 0)
			end
			return
		end
		local toCancel, i = {}, 0
		local cancelled = 0
		local armCancel
		armCancel = function(k)
			if token ~= cancelToken then
				return
			end
			if k > #toCancel then
				if FL.Secure and FL.Secure.Disarm and not InCombatLockdown() then
					FL.Secure.Disarm("cancel")
				end
				FL:Print("Undercut check done: %d of %d auctions flagged, %d cancel clicks issued.", #toCancel, nItems, cancelled)
				FL.Fire("FL_POSTING_CANCEL_DONE", #toCancel, cancelled)
				if onDone then
					pcall(onDone, #toCancel, cancelled)
				end
				return
			end
			if InCombatLockdown() then
				FL:Warn("Combat lockdown; cancel the remaining %d auctions after combat.", #toCancel - k + 1)
				return
			end
			local c = toCancel[k]
			FL.Secure.Arm("cancel", {
				label = format("CANCEL %s @ %s", ItemName(c.itemID), M(c.unit, true)),
				fn = function()
					if C_AuctionHouse.CanCancelAuction and not C_AuctionHouse.CanCancelAuction(c.auctionID) then
						error("auction cannot be cancelled")
					end
					C_AuctionHouse.CancelAuction(c.auctionID)
					cancelled = cancelled + 1
					After(0.5, function() armCancel(k + 1) end)
				end,
				onFail = function(err)
					FL:Warn("Cancel failed for %s: %s", ItemName(c.itemID), tostring(err))
					After(0.3, function() armCancel(k + 1) end)
				end,
			})
			FL.Fire("FL_POSTING_CANCEL_ARMED", c, k, #toCancel)
		end
		local step
		step = function()
			if token ~= cancelToken then
				return
			end
			i = i + 1
			if i > nItems then
				armCancel(1)
				return
			end
			local itemID = items[i]
			local done = false
			local function finish(results)
				if done or token ~= cancelToken then
					return
				end
				done = true
				local competitorMin = CompetitorMin(results)
				if competitorMin then
					local list = byItem[itemID]
					for k = 1, #list do
						if list[k].unit > competitorMin then
							list[k].competitorMin = competitorMin
							toCancel[#toCancel + 1] = list[k]
						end
					end
				end
				step()
			end
			local ok = pcall(scan.ScanItem, scan, itemID, function(_, results) finish(results) end)
			if not ok then
				finish(nil)
				return
			end
			After(PRICE_SCAN_TIMEOUT, function()
				if not done then
					finish(nil)
				end
			end)
		end
		step()
	end)
	return true
end

-- Reset posting state when the AH closes.
local function ResetPosting()
	pricingToken = pricingToken + 1
	cancelToken = cancelToken + 1
	pricingActive = false
	Posting.armedEntry = nil
	if FL.Secure and FL.Secure.Disarm and not InCombatLockdown() then
		FL.Secure.Disarm("post")
		FL.Secure.Disarm("cancel")
	end
end

-- FL.Posting:IsPricing() -> boolean
function Posting:IsPricing()
	return pricingActive
end

-------------------------------------------------------------------------------
-- §6.6 FL.Crafting — recipe storage
-------------------------------------------------------------------------------
local recipeIndex = {}
local recipeIndexBuilt = false
local reagentParts = {}
local reagentScratch0 = {}
local reagentScratch1 = {}
local reagentScratchQ = {}
local craftCostMemo = {}
local craftGuard = {}
local tradeSkillOpen = false
local recipeFields = {}

-- FL.Crafting.ParseReagents(str, out) -> array of {itemID=, qty=} (out.n set; out reused)
function Crafting.ParseReagents(str, out)
	out = out or {}
	local n = 0
	if type(str) == "string" and str ~= "" then
		for id, qty in gmatch(str, "(%d+):(%d+)") do
			n = n + 1
			local e = out[n]
			if type(e) ~= "table" then
				e = {}
				out[n] = e
			end
			e.itemID = tonumber(id)
			e.qty = tonumber(qty) or 1
		end
	end
	for i = n + 1, #out do
		out[i] = nil
	end
	out.n = n
	return out
end

-- Rebuild the outputItemID → recipe rowIDs index.
local function RebuildRecipeIndex()
	wipe(recipeIndex)
	wipe(craftCostMemo)
	local db = FL.DB and FL.DB.recipes
	if db then
		db:ForEach(function(rid)
			local outputItemID = db:Get(rid, "outputItemID")
			if outputItemID and outputItemID > 0 and db:Get(rid, "learned") ~= false then
				local list = recipeIndex[outputItemID]
				if not list then
					list = {}
					recipeIndex[outputItemID] = list
				end
				list[#list + 1] = rid
			end
		end)
	end
	recipeIndexBuilt = true
end

-- Upsert one recipe row from assembled fields.
local function StoreRecipe(db, recipeID, name, profession, outputItemID, numMin, numMax, reagentsStr, now)
	wipe(recipeFields)
	recipeFields.recipeID = recipeID
	recipeFields.name = tostring(name or "")
	recipeFields.profession = tostring(profession or "")
	recipeFields.outputItemID = outputItemID
	recipeFields.numMin = (tonumber(numMin) and tonumber(numMin) > 0) and floor(tonumber(numMin)) or 1
	recipeFields.numMax = (tonumber(numMax) and tonumber(numMax) > 0) and floor(tonumber(numMax)) or recipeFields.numMin
	recipeFields.reagentsStr = reagentsStr
	recipeFields.learned = true
	recipeFields.charKey = FL.playerKey or ""
	recipeFields.ts = now
	db:Upsert("recipeID", recipeID, recipeFields)
end

-- Modern C_TradeSkillUI path for one recipe; returns true when stored.
local function ScanModernRecipe(db, recipeID, profession, now)
	local info = C_TradeSkillUI.GetRecipeInfo(recipeID)
	if not info or not info.learned then
		return false
	end
	local schematic
	if C_TradeSkillUI.GetRecipeSchematic then
		local ok, result = pcall(C_TradeSkillUI.GetRecipeSchematic, recipeID, false)
		if ok then
			schematic = result
		end
	end
	local outputItemID = schematic and tonumber(schematic.outputItemID) or 0
	if outputItemID == 0 and C_TradeSkillUI.GetRecipeItemLink then
		local link = C_TradeSkillUI.GetRecipeItemLink(recipeID)
		outputItemID = link and FL.ItemIDFromLink(link) or 0
	end
	if outputItemID == 0 then
		return false
	end
	local basic = (Enum and Enum.CraftingReagentType and Enum.CraftingReagentType.Basic) or 1
	local n = 0
	local slots = schematic and schematic.reagentSlotSchematics
	if slots then
		for i = 1, #slots do
			local slot = slots[i]
			if (slot.reagentType == nil or slot.reagentType == basic) and slot.required ~= false then
				local reagent = slot.reagents and slot.reagents[1]
				if reagent and reagent.itemID then
					n = n + 1
					reagentParts[n] = reagent.itemID .. ":" .. (slot.quantityRequired or 1)
				end
			end
		end
	end
	if n == 0 then
		return false
	end
	local reagentsStr = tconcat(reagentParts, ";", 1, n)
	local numMin = schematic and schematic.quantityMin or 1
	local numMax = schematic and schematic.quantityMax or numMin
	StoreRecipe(db, recipeID, info.name or (schematic and schematic.name), profession, outputItemID, numMin, numMax, reagentsStr, now)
	return true
end

-- Classic GetTradeSkill* path for one list index; returns true when stored.
local function ScanClassicRecipe(db, index, profession, now)
	local name, skillType = GetTradeSkillInfo(index)
	if not name or skillType == "header" or skillType == "subheader" then
		return false
	end
	local link = GetTradeSkillItemLink and GetTradeSkillItemLink(index)
	local outputItemID = link and FL.ItemIDFromLink(link)
	if not outputItemID or outputItemID == 0 then
		return false
	end
	local recipeID
	if GetTradeSkillRecipeLink then
		local rlink = GetTradeSkillRecipeLink(index)
		recipeID = rlink and tonumber(strmatch(rlink, "enchant:(%d+)"))
	end
	if not recipeID then
		recipeID = -outputItemID
	end
	local numMin, numMax = 1, 1
	if GetTradeSkillNumMade then
		local a, b = GetTradeSkillNumMade(index)
		numMin, numMax = tonumber(a) or 1, tonumber(b) or tonumber(a) or 1
	end
	local n = 0
	local numReagents = GetTradeSkillNumReagents and GetTradeSkillNumReagents(index) or 0
	for r = 1, numReagents do
		local _, _, count = GetTradeSkillReagentInfo(index, r)
		local rlink = GetTradeSkillReagentItemLink and GetTradeSkillReagentItemLink(index, r)
		local reagentID = rlink and FL.ItemIDFromLink(rlink)
		if reagentID then
			n = n + 1
			reagentParts[n] = reagentID .. ":" .. (tonumber(count) or 1)
		end
	end
	if n == 0 then
		return false
	end
	StoreRecipe(db, recipeID, name, profession, outputItemID, numMin, numMax, tconcat(reagentParts, ";", 1, n), now)
	return true
end

-- FL.Crafting.ScanOpenProfession() -- record learned recipes of the open profession window
function Crafting.ScanOpenProfession()
	local db = FL.DB and FL.DB.recipes
	if not db then
		return 0
	end
	local now = time()
	local count = 0
	local profession = "profession"
	if C_TradeSkillUI and C_TradeSkillUI.GetAllRecipeIDs and C_TradeSkillUI.GetRecipeInfo then
		if C_TradeSkillUI.IsTradeSkillReady and not C_TradeSkillUI.IsTradeSkillReady() then
			return 0
		end
		if C_TradeSkillUI.IsTradeSkillLinked and C_TradeSkillUI.IsTradeSkillLinked() then
			return 0
		end
		if C_TradeSkillUI.IsTradeSkillGuild and C_TradeSkillUI.IsTradeSkillGuild() then
			return 0
		end
		if C_TradeSkillUI.GetBaseProfessionInfo then
			local ok, info = pcall(C_TradeSkillUI.GetBaseProfessionInfo)
			if ok and info and info.professionName then
				profession = info.professionName
			end
		end
		local ids = C_TradeSkillUI.GetAllRecipeIDs() or EMPTY
		for i = 1, #ids do
			local ok, stored = pcall(ScanModernRecipe, db, ids[i], profession, now)
			if ok and stored then
				count = count + 1
			end
		end
	elseif GetNumTradeSkills and GetTradeSkillInfo then
		if GetTradeSkillLine then
			local name = GetTradeSkillLine()
			if type(name) == "string" and name ~= "" then
				profession = name
			end
		end
		local n = GetNumTradeSkills() or 0
		for i = 1, n do
			local ok, stored = pcall(ScanClassicRecipe, db, i, profession, now)
			if ok and stored then
				count = count + 1
			end
		end
	else
		return 0
	end
	RebuildRecipeIndex()
	if count > 0 then
		FL:Print("Learned %d recipes for %s.", count, profession)
	end
	FL.Fire("FL_RECIPES_UPDATED", profession, count)
	return count
end

-------------------------------------------------------------------------------
-- §6.6 FL.Crafting — costing
-------------------------------------------------------------------------------
-- Unit cost of one recipe row; depth 1 reagents use the mat formula only.
local function RecipeUnitCost(db, rid, depth)
	local parsed = depth == 0 and reagentScratch0 or reagentScratch1
	Crafting.ParseReagents(db:Get(rid, "reagentsStr"), parsed)
	if parsed.n == 0 then
		return nil
	end
	local matFormula = SS("crafting").matFormula or "matprice"
	local total = 0
	for i = 1, parsed.n do
		local rg = parsed[i]
		local cost = Eval(matFormula, rg.itemID)
		if depth == 0 and recipeIndex[rg.itemID] and not craftGuard[rg.itemID] then
			craftGuard[rg.itemID] = true
			local rows = recipeIndex[rg.itemID]
			local sub
			for k = 1, #rows do
				local c = RecipeUnitCost(db, rows[k], 1)
				if c and (not sub or c < sub) then
					sub = c
				end
			end
			craftGuard[rg.itemID] = nil
			if sub and (not cost or sub < cost) then
				cost = sub
			end
		end
		if not cost or cost <= 0 then
			return nil
		end
		total = total + cost * rg.qty
	end
	local numMin = db:Get(rid, "numMin")
	if not numMin or numMin < 1 then
		numMin = 1
	end
	return total / numMin
end

-- Cheapest recipe (rowID, unit cost) for an item at the given depth.
local function CheapestRecipe(itemID, depth)
	if not recipeIndexBuilt then
		RebuildRecipeIndex()
	end
	local rows = recipeIndex[itemID]
	local db = FL.DB and FL.DB.recipes
	if not rows or not db or craftGuard[itemID] then
		return nil, nil
	end
	craftGuard[itemID] = true
	local bestRow, bestCost
	for k = 1, #rows do
		local cost = RecipeUnitCost(db, rows[k], depth)
		if cost and (not bestCost or cost < bestCost) then
			bestRow, bestCost = rows[k], cost
		end
	end
	craftGuard[itemID] = nil
	return bestRow, bestCost
end

-- FL.Crafting.GetCraftCost(itemID) -> copper|nil (cheapest known recipe)
function Crafting.GetCraftCost(itemID)
	if not itemID then
		return nil
	end
	local tick = FL.FrameTick or 0
	local memo = craftCostMemo[itemID]
	if memo and memo.tick == tick then
		return memo.value
	end
	local _, cost = CheapestRecipe(itemID, 0)
	if cost then
		cost = floor(cost + 0.5)
		if cost < 1 then
			cost = nil
		end
	end
	if craftGuard[itemID] then
		return cost
	end
	if not memo then
		memo = {}
		craftCostMemo[itemID] = memo
	end
	memo.tick = tick
	memo.value = cost
	return cost
end

-- FL.Crafting.GetRecipeFor(itemID) -> rowID|nil (cheapest recipe, or the first known)
function Crafting.GetRecipeFor(itemID)
	if not itemID then
		return nil
	end
	local rid = CheapestRecipe(itemID, 0)
	if rid then
		return rid
	end
	if not recipeIndexBuilt then
		RebuildRecipeIndex()
	end
	local rows = recipeIndex[itemID]
	return rows and rows[1] or nil
end

-------------------------------------------------------------------------------
-- §6.6 FL.Crafting — queue, shopping list, crafting, buying
-------------------------------------------------------------------------------
-- Queue ordering: margin desc, then profit*velocity desc, then itemID.
local function QueueLess(a, b)
	if a.marginPct ~= b.marginPct then
		return a.marginPct > b.marginPct
	end
	local va, vb = a.profit * a.soldPerDay, b.profit * b.soldPerDay
	if va ~= vb then
		return va > vb
	end
	return a.itemID < b.itemID
end

-- FL.Crafting:BuildQueue() -> array of entries sorted by marginPct desc
function Crafting:BuildQueue()
	local queue = {}
	local db = FL.DB and FL.DB.recipes
	if not db then
		Crafting.queue = queue
		return queue
	end
	if not recipeIndexBuilt then
		RebuildRecipeIndex()
	end
	local cs = SS("crafting")
	local target = floor(tonumber(cs.restockTarget) or 5)
	local minProfit = Money(cs.minProfit, 1000)
	local minMargin = tonumber(cs.minMarginPct) or 10
	local valueFormula = cs.valueFormula or "max(dbminbuyout, dbmarket)"
	local matFormula = cs.matFormula or "matprice"
	local cut = AHCut()
	for itemID in pairs(recipeIndex) do
		local rid, rawCost = CheapestRecipe(itemID, 0)
		local cost = rawCost and floor(rawCost + 0.5) or nil
		if rid and cost and cost > 0 then
			local value = Eval(valueFormula, itemID)
			if value and value > 0 then
				value = value * (1 - cut)
				local profit = value - cost
				local marginPct = profit / cost * 100
				local have = Inventory.Total(itemID)
				local toCraft = mmax(0, target - have)
				if profit >= minProfit and marginPct >= minMargin and toCraft > 0 then
					local numMin = db:Get(rid, "numMin")
					if not numMin or numMin < 1 then
						numMin = 1
					end
					local crafts = ceil(toCraft / numMin)
					Crafting.ParseReagents(db:Get(rid, "reagentsStr"), reagentScratchQ)
					local mats = {}
					for i = 1, reagentScratchQ.n do
						local rg = reagentScratchQ[i]
						local need = rg.qty * crafts
						local haveMat = Inventory.Here(rg.itemID)
						local unitCost = Eval(matFormula, rg.itemID)
						if recipeIndex[rg.itemID] then
							local _, sub = CheapestRecipe(rg.itemID, 1)
							if sub and (not unitCost or sub < unitCost) then
								unitCost = sub
							end
						end
						mats[i] = { itemID = rg.itemID, need = need, have = haveMat, buy = mmax(0, need - haveMat), unitCost = floor((unitCost or 0) + 0.5) }
					end
					local name = db:Get(rid, "name")
					if not name or name == "" then
						name = ItemName(itemID)
					end
					queue[#queue + 1] = {
						recipeID = db:Get(rid, "recipeID"),
						itemID = itemID,
						name = name,
						cost = cost,
						value = floor(value + 0.5),
						profit = floor(profit + 0.5),
						marginPct = marginPct,
						soldPerDay = (FL.Market and FL.Market.SoldPerDay(itemID)) or 0,
						have = have,
						target = target,
						toCraft = toCraft,
						crafts = crafts,
						numMin = numMin,
						mats = mats,
					}
				end
			end
		end
	end
	tsort(queue, QueueLess)
	Crafting.queue = queue
	FL.Fire("FL_CRAFTING_QUEUE", #queue)
	return queue
end

-- FL.Crafting:ShoppingList(queue) -> array of { itemID, need, have, buy, unitCost, total }
function Crafting:ShoppingList(queue)
	queue = queue or Crafting.queue or self:BuildQueue()
	local agg, order, n = {}, {}, 0
	for i = 1, #queue do
		local mats = queue[i].mats
		for k = 1, #mats do
			local m = mats[k]
			local row = agg[m.itemID]
			if not row then
				row = { itemID = m.itemID, need = 0, have = Inventory.Here(m.itemID), buy = 0, unitCost = m.unitCost or 0, total = 0, vendor = false }
				agg[m.itemID] = row
				n = n + 1
				order[n] = row
			end
			row.need = row.need + m.need
			if (m.unitCost or 0) > 0 and (row.unitCost == 0 or m.unitCost < row.unitCost) then
				row.unitCost = m.unitCost
			end
		end
	end
	local includeVendor = SS("crafting").includeVendorMats ~= false
	local list = {}
	for i = 1, n do
		local row = order[i]
		row.buy = mmax(0, row.need - row.have)
		row.total = row.buy * row.unitCost
		row.vendor = Vendor.BuyPrice(row.itemID) ~= nil
		row.name = ItemName(row.itemID)
		if row.buy > 0 and (includeVendor or not row.vendor) then
			list[#list + 1] = row
		end
	end
	tsort(list, function(a, b)
		if a.total ~= b.total then
			return a.total > b.total
		end
		return a.itemID < b.itemID
	end)
	return list
end

-- FL.Crafting:CraftNext(entry) -- craft the entry from an open profession window
function Crafting:CraftNext(entry)
	if type(entry) ~= "table" or not entry.itemID then
		return false
	end
	local name = entry.name or ItemName(entry.itemID)
	if not tradeSkillOpen then
		FL:Print("Open the profession window to craft %s.", name)
		return false
	end
	local crafts = mmax(1, floor(tonumber(entry.crafts) or ceil((tonumber(entry.toCraft) or 1) / mmax(1, tonumber(entry.numMin) or 1))))
	local recipeID = tonumber(entry.recipeID) or 0
	if C_TradeSkillUI and C_TradeSkillUI.CraftRecipe and C_TradeSkillUI.GetRecipeInfo and recipeID > 0 then
		local info = C_TradeSkillUI.GetRecipeInfo(recipeID)
		if not info or not info.learned then
			FL:Print("%s is not available in the open profession window.", name)
			return false
		end
		if info.numAvailable and info.numAvailable > 0 then
			crafts = mmin(crafts, info.numAvailable)
		elseif info.craftable == false or info.numAvailable == 0 then
			FL:Warn("Missing reagents for %s.", name)
			return false
		end
		local ok, err = pcall(C_TradeSkillUI.CraftRecipe, recipeID, crafts)
		if not ok then
			FL:Warn("Craft failed: %s", tostring(err))
			return false
		end
		FL:Print("Crafting %d x %s.", crafts, name)
		return true
	elseif DoTradeSkill and GetNumTradeSkills and GetTradeSkillInfo then
		local n = GetNumTradeSkills() or 0
		for i = 1, n do
			local skillName, skillType, numAvailable = GetTradeSkillInfo(i)
			if skillName == name and skillType ~= "header" and skillType ~= "subheader" then
				numAvailable = tonumber(numAvailable) or 0
				if numAvailable <= 0 then
					FL:Warn("Missing reagents for %s.", name)
					return false
				end
				crafts = mmin(crafts, numAvailable)
				DoTradeSkill(i, crafts)
				FL:Print("Crafting %d x %s.", crafts, name)
				return true
			end
		end
		FL:Print("%s is not in the open profession window.", name)
		return false
	end
	FL:Print("Open the profession window to craft %s.", name)
	return false
end

-- Buy one shopping-list row through the sniper popup, then continue with the next.
local function BuyMatStep(list, i)
	local scan = FL.AuctionScan
	while i <= #list and ((list[i].buy or 0) <= 0 or list[i].vendor) do
		i = i + 1
	end
	if i > #list then
		FL:Print("Shopping list complete.")
		PopupStatus("Shopping list complete.", 0.3, 1, 0.3)
		After(1.0, function()
			if Sniper.currentDeal and Sniper.currentDeal.isMat then
				Sniper.currentDeal = nil
				PopupNext()
			end
		end)
		return
	end
	local mat = list[i]
	local itemID = mat.itemID
	if not IsCommodityKey(nil, itemID, mat.buy) then
		FL:Print("%s is not a commodity; buy it manually.", ItemLinkOrName(itemID))
		return BuyMatStep(list, i + 1)
	end
	local deal = {
		itemID = itemID,
		suffix = 0,
		unitPrice = mat.unitCost or 0,
		quantity = mat.buy,
		requested = mat.buy,
		marketValue = (FL.Market and FL.Market.MarketValue(itemID)) or mat.unitCost or 0,
		threshold = mat.unitCost or 0,
		isCommodity = true,
		profit = 0,
		ts = time(),
		isMat = true,
		onSkip = function() BuyMatStep(list, i + 1) end,
	}
	if not PopupShowDeal(deal) then
		return
	end
	PopupStatus(format("Fetching prices for %s...", mat.name or ItemName(itemID)))
	buyToken = buyToken + 1
	local token = buyToken
	local function proceed(results)
		if token ~= buyToken or Sniper.currentDeal ~= deal then
			return
		end
		if not results and scan.GetLastResults then
			results = scan.GetLastResults(itemID)
		end
		local n = results and results.n or 0
		local prices, qtys, own = results and results.unitPrices, results and results.quantities, results and results.own
		if n <= 0 or not prices or not qtys then
			deal.statusText = "No auctions found. Skip to continue."
			PopupStatus(deal.statusText, 1, 0.6, 0.2)
			return
		end
		wipe(ladderOrder)
		for k = 1, n do
			ladderOrder[k] = k
		end
		ladderPrices = prices
		tsort(ladderOrder, LadderLess)
		local needed = mat.buy
		local cum, limit = 0, nil
		for k = 1, n do
			local idx = ladderOrder[k]
			if not (own and own[idx]) then
				cum = cum + (qtys[idx] or 0)
				limit = prices[idx]
				if cum >= needed then
					break
				end
			end
		end
		if not limit or cum <= 0 then
			deal.statusText = "No auctions found. Skip to continue."
			PopupStatus(deal.statusText, 1, 0.6, 0.2)
			return
		end
		local qty = mmin(needed, cum)
		local expected = (mat.unitCost or 0) > 0 and mat.unitCost * 1.25 or huge
		deal.unitPrice = limit
		deal.quantity = cum
		if popup and popup.price then
			popup.price:SetText(format("Up to %s per unit · expected %s", M(limit), M(mat.unitCost or 0)))
			popup.profit:SetText(format("Need %d, have %d, buying %d", mat.need or qty, mat.have or 0, qty))
			popup.qty:SetText(tostring(qty))
		end
		if limit > expected then
			deal.statusText = format("Too expensive: %s per unit vs expected %s. Skip to continue.", M(limit, true), M(mat.unitCost, true))
			PopupStatus(deal.statusText, 1, 0.6, 0.2)
			return
		end
		deal.statusText = format("%d available up to %s. Click BUY, then CONFIRM.", qty, M(limit, true))
		PopupStatus(deal.statusText, 0.6, 1, 0.6)
		scan:BeginCommodityPurchase(itemID, qty, limit, function(ok, reason, unit)
			if ok then
				FL:Print("Bought %d x %s for %s.", qty, ItemLinkOrName(itemID), M((unit or limit) * qty))
				mat.have = (mat.have or 0) + qty
				mat.buy = mmax(0, mat.buy - qty)
				PopupStatus("Bought. Moving to the next material...", 0.3, 1, 0.3)
				After(0.8, function()
					if Sniper.currentDeal == deal then
						BuyMatStep(list, i + 1)
					end
				end)
			else
				deal.statusText = "Purchase failed: " .. tostring(reason or "unknown")
				PopupStatus(deal.statusText, 1, 0.4, 0.4)
			end
		end)
	end
	local ok, err = pcall(scan.ScanItem, scan, itemID, function(_, results) proceed(results) end)
	if not ok then
		FL:Warn("Could not query %s: %s", ItemLinkOrName(itemID), tostring(err))
	end
end

-- FL.Crafting:BuyMats(list) -- sequential commodity purchases for a shopping list
function Crafting:BuyMats(list)
	if not (FL.AuctionScan and FL.AuctionScan.isOpen and FL.AuctionScan.BeginCommodityPurchase) then
		FL:Warn("Open the Auction House before buying materials.")
		return false
	end
	if InCombatLockdown() then
		FL:Warn("Cannot buy materials in combat.")
		return false
	end
	list = list or self:ShoppingList()
	if #list == 0 then
		FL:Print("Nothing to buy.")
		return false
	end
	FL:Print("Buying materials for %d items; click BUY then CONFIRM for each.", #list)
	BuyMatStep(list, 1)
	return true
end

-- @@CONTINUE@@
