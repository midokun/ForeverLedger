local addonName, FL = ...

--------------------------------------------------------------------------------
-- Tooltips.lua
-- ForeverLedger item tooltip annotations (SPEC §7). Registers a post-call on
-- the modern TooltipDataProcessor (falling back to OnTooltipSetItem hooks on
-- older clients) and appends up to nine data lines to item tooltips: market
-- value, min buyout, historical, crafting cost, vendor prices, sale rate,
-- cross-character inventory, ledger averages and last-scan age.
-- The per-tooltip path creates no tables: every value is read into locals and
-- formatted straight into the tooltip.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Cached globals
--------------------------------------------------------------------------------
local _G = _G
local type, tonumber, tostring, pcall = type, tonumber, tostring, pcall
local floor, abs = math.floor, math.abs
local format, strfind = string.format, string.find
local time, GetTime = time, GetTime
local IsShiftKeyDown = IsShiftKeyDown
local C_Item = C_Item
local Enum = Enum
local TooltipDataProcessor = TooltipDataProcessor
local TooltipUtil = TooltipUtil
local GameTooltip = GameTooltip
local GetItemCountAPI = (C_Item and C_Item.GetItemCount) or GetItemCount

--------------------------------------------------------------------------------
-- Module table
--------------------------------------------------------------------------------
FL.Tooltip = FL.Tooltip or {}
local Tooltip = FL.Tooltip

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------
local LABEL_COLOR = "|cff80c0ff"
local GREY = "|cff9d9d9d"
local GREEN = "|cff00ff00"
local RED = "|cffff2020"
local COLOR_END = "|r"

-- Left-column label colour as RGB (matches |cff80c0ff).
local LR, LG, LB = 0.502, 0.753, 1.0
-- Right-column base colour (values carry their own money/colour escapes).
local RR, RG, RB = 1.0, 1.0, 1.0

-- Pre-built labels so the per-tooltip path never concatenates them.
local LABEL_MARKET = LABEL_COLOR .. "FL Market Value" .. COLOR_END
local LABEL_MINBUYOUT = LABEL_COLOR .. "FL Min Buyout" .. COLOR_END
local LABEL_HISTORICAL = LABEL_COLOR .. "FL Historical" .. COLOR_END
local LABEL_CRAFTING = LABEL_COLOR .. "FL Crafting Cost" .. COLOR_END
local LABEL_VENDOR = LABEL_COLOR .. "FL Vendor" .. COLOR_END
local LABEL_SOLDPERDAY = LABEL_COLOR .. "FL Sold/Day" .. COLOR_END
local LABEL_INVENTORY = LABEL_COLOR .. "FL Inventory" .. COLOR_END
local LABEL_LEDGER = LABEL_COLOR .. "FL Ledger" .. COLOR_END
local LABEL_LASTSCAN = LABEL_COLOR .. "FL Last Scan" .. COLOR_END

-- Only these tooltips are annotated (SPEC §0 / §7).
local TOOLTIP_NAMES = {
	"GameTooltip",
	"ItemRefTooltip",
	"ShoppingTooltip1",
	"ShoppingTooltip2",
	"ItemRefShoppingTooltip1",
	"ItemRefShoppingTooltip2",
}
local ALLOWED_TOOLTIPS = {}
for i = 1, #TOOLTIP_NAMES do
	ALLOWED_TOOLTIPS[TOOLTIP_NAMES[i]] = true
end

-- Historical line is shown only when it differs from market by more than this.
local HISTORICAL_DIFF_PCT = 0.10
-- Deal score threshold for the " · Deal <score>" suffix on the Sold/Day line.
local DEAL_SCORE_MIN = 60
-- Default AH consignment cut when settings are not yet hydrated.
local DEFAULT_AH_CUT = 0.05

--------------------------------------------------------------------------------
-- State
--------------------------------------------------------------------------------
-- Double-processing guard: the same tooltip+item within the same frame tick is
-- skipped (TooltipDataProcessor and legacy hooks can both fire twice per set).
local lastTooltip, lastItemID, lastTick = nil, nil, -1
local installed = false
local installMode = "none"
local warnedError = false

-- Inventory accumulators (upvalues so the ForEachCharacter callback allocates
-- nothing per tooltip).
local invBags, invBank, invMail, invAH, invAlts = 0, 0, 0, 0, 0

--------------------------------------------------------------------------------
-- Small helpers
--------------------------------------------------------------------------------

-- Coerce a possibly-nil / NaN value to a usable number (0 when absent).
local function Num(v)
	if type(v) ~= "number" or v ~= v then
		return 0
	end
	return v
end

-- Live settings root: FL.Settings after hydration, RuntimeDB before, defaults last.
local function SettingsRoot()
	local s = FL.Settings
	if s then
		return s
	end
	local root = FL.RuntimeDB
	if root and root.settings then
		return root.settings
	end
	return FL.DefaultSettings
end

-- The tooltip settings sub-table or nil when nothing is available yet.
local function TooltipSettings()
	local s = SettingsRoot()
	return s and s.tooltip or nil
end

-- A toggle counts as on unless it is explicitly false (missing keys = default on).
local function IsOn(v)
	return v ~= false
end

-- Current AH cut (fraction) from settings.market.ahCut.
local function AhCut()
	local s = SettingsRoot()
	local m = s and s.market
	local cut = m and tonumber(m.ahCut)
	if not cut or cut < 0 or cut >= 1 then
		cut = DEFAULT_AH_CUT
	end
	return cut
end

-- Money formatter routed through Core (resolved at call time).
local function Money(copper, noColor)
	return FL.FormatMoney(copper, noColor)
end

-- "just now" / "12m ago" / "3h ago" / "2d ago" for an age in seconds.
local function RelativeTime(seconds)
	if seconds < 0 then
		seconds = 0
	end
	if seconds < 60 then
		return "just now"
	elseif seconds < 3600 then
		return format("%dm ago", floor(seconds / 60))
	elseif seconds < 86400 then
		return format("%dh ago", floor(seconds / 3600))
	end
	return format("%dd ago", floor(seconds / 86400))
end

-- Read one market column for itemID, honouring the link suffix when a row for
-- that exact suffix exists and falling back to the generic row otherwise.
local function MarketField(itemID, field, suffix)
	local Market = FL.Market
	if not Market or type(Market.Get) ~= "function" then
		return nil
	end
	if suffix and suffix ~= 0 then
		local v = Market.Get(itemID, field, suffix)
		if v ~= nil then
			return v
		end
	end
	return Market.Get(itemID, field, nil)
end

-- Append one label/value pair with the standard colours.
local function AddDouble(tooltip, label, right)
	tooltip:AddDoubleLine(label, right, LR, LG, LB, RR, RG, RB)
end

--------------------------------------------------------------------------------
-- Data getters (each returns nil / 0 when the source is unavailable)
--------------------------------------------------------------------------------

-- 7-day market trend in percent, or nil when FL.Intel cannot compute one.
local function GetTrend(itemID)
	local Intel = FL.Intel
	if Intel and type(Intel.Trend) == "function" then
		local pct = Intel.Trend(itemID)
		if type(pct) == "number" and pct == pct then
			return pct
		end
	end
	return nil
end

-- Deal score 0..100 or nil.
local function GetDealScore(itemID)
	local Intel = FL.Intel
	if Intel and type(Intel.DealScore) == "function" then
		local score = Intel.DealScore(itemID)
		if type(score) == "number" and score == score then
			return score
		end
	end
	return nil
end

-- Cheapest crafting cost in copper or nil.
local function GetCraftCost(itemID)
	local Crafting = FL.Crafting
	if Crafting and type(Crafting.GetCraftCost) == "function" then
		local cost = Crafting.GetCraftCost(itemID)
		if type(cost) == "number" and cost == cost and cost > 0 then
			return cost
		end
	end
	return nil
end

-- Vendor sell price and vendor buy price (either may be nil).
local function GetVendorPrices(itemID)
	local sell, buy
	local Vendor = FL.Vendor
	if Vendor then
		if type(Vendor.SellPrice) == "function" then
			sell = Vendor.SellPrice(itemID)
		end
		if type(Vendor.BuyPrice) == "function" then
			buy = Vendor.BuyPrice(itemID)
		end
	end
	if sell == nil and type(FL.GetItemSellPrice) == "function" then
		sell = FL.GetItemSellPrice(itemID)
	end
	sell = Num(sell)
	buy = Num(buy)
	if sell <= 0 then
		sell = nil
	end
	if buy <= 0 then
		buy = nil
	end
	return sell, buy
end

-- Weighted ledger averages (copper) for purchases and sales; either may be nil.
local function GetLedgerAverages(itemID)
	local Ledger = FL.Ledger
	if not Ledger then
		return nil, nil
	end
	local avgBuy, avgSell
	if type(Ledger.AvgBuy) == "function" then
		avgBuy = Num(Ledger.AvgBuy(itemID))
		if avgBuy <= 0 then
			avgBuy = nil
		end
	end
	if type(Ledger.AvgSell) == "function" then
		avgSell = Num(Ledger.AvgSell(itemID))
		if avgSell <= 0 then
			avgSell = nil
		end
	end
	return avgBuy, avgSell
end

-- ForEachCharacter callback: splits counts into this character vs. alts.
local function InventoryAccumulate(charKey, bags, bank, mail, auctions)
	bags = Num(bags)
	bank = Num(bank)
	mail = Num(mail)
	auctions = Num(auctions)
	if charKey == FL.playerKey then
		invBags = invBags + bags
		invBank = invBank + bank
		invMail = invMail + mail
		invAH = invAH + auctions
	else
		invAlts = invAlts + bags + bank + mail + auctions
	end
end

-- Fill the inv* upvalues for itemID. Uses FL.Inventory rows when present and
-- the live container count for this character's bags; falls back to
-- C_Item.GetItemCount when AdvancedFeatures is unavailable.
local function CollectInventory(itemID)
	invBags, invBank, invMail, invAH, invAlts = 0, 0, 0, 0, 0
	local Inv = FL.Inventory
	if Inv and type(Inv.ForEachCharacter) == "function" then
		Inv.ForEachCharacter(itemID, InventoryAccumulate)
		if type(Inv.Here) == "function" then
			local here = Inv.Here(itemID)
			if type(here) == "number" and here == here and here >= 0 then
				invBags = here
			end
		end
		return
	end
	if GetItemCountAPI then
		local bags = Num(GetItemCountAPI(itemID))
		local withBank = Num(GetItemCountAPI(itemID, true))
		invBags = bags
		if withBank > bags then
			invBank = withBank - bags
		end
	end
end

--------------------------------------------------------------------------------
-- Public: line builder
--------------------------------------------------------------------------------

-- Append the ForeverLedger lines for itemID (+ optional link suffix) to any
-- tooltip; respects the per-line toggles, returns the number of lines added.
function Tooltip.AddLines(tooltip, itemID, suffix)
	if not tooltip or type(tooltip.AddDoubleLine) ~= "function" then
		return 0
	end
	if tooltip.IsForbidden and tooltip:IsForbidden() then
		return 0
	end
	itemID = tonumber(itemID)
	if not itemID or itemID <= 0 then
		return 0
	end
	local ts = TooltipSettings()
	if not ts then
		return 0
	end
	suffix = tonumber(suffix) or 0
	local added = 0
	local showMarket = IsOn(ts.showMarket)

	local marketValue = Num(MarketField(itemID, "marketValue", suffix))

	-- 1. FL Market Value (+ trend)
	if showMarket and marketValue > 0 then
		local right = Money(marketValue)
		local trend = GetTrend(itemID)
		if trend then
			right = format("%s %s(%+.1f%%)%s", right, (trend >= 0) and GREEN or RED, trend, COLOR_END)
		end
		AddDouble(tooltip, LABEL_MARKET, right)
		added = added + 1
	end

	-- 2. FL Min Buyout (+ auction count)
	if IsOn(ts.showMinBuyout) then
		local minBuyout = Num(MarketField(itemID, "minBuyout", suffix))
		if minBuyout > 0 then
			local numAuctions = floor(Num(MarketField(itemID, "numAuctions", suffix)))
			local right
			if numAuctions > 0 then
				right = format("%s %s(x%d)%s", Money(minBuyout), GREY, numAuctions, COLOR_END)
			else
				right = Money(minBuyout)
			end
			AddDouble(tooltip, LABEL_MINBUYOUT, right)
			added = added + 1
		end
	end

	-- 3. FL Historical (only when it differs from market by > 10%)
	if showMarket then
		local historical = Num(MarketField(itemID, "historical", suffix))
		if historical > 0 then
			local differs
			if marketValue > 0 then
				differs = abs(historical - marketValue) > marketValue * HISTORICAL_DIFF_PCT
			else
				differs = true
			end
			if differs then
				AddDouble(tooltip, LABEL_HISTORICAL, Money(historical))
				added = added + 1
			end
		end
	end

	-- 4. FL Crafting Cost (+ profit after AH cut)
	if IsOn(ts.showCrafting) then
		local cost = GetCraftCost(itemID)
		if cost then
			local right
			if marketValue > 0 then
				local profit = marketValue * (1 - AhCut()) - cost
				right = format("%s  profit %s%s%s", Money(cost), (profit >= 0) and GREEN or RED, Money(floor(profit), true), COLOR_END)
			else
				right = Money(cost)
			end
			AddDouble(tooltip, LABEL_CRAFTING, right)
			added = added + 1
		end
	end

	-- 5. FL Vendor (sell price, and buy price when known)
	if IsOn(ts.showVendor) then
		local sell, buy = GetVendorPrices(itemID)
		if sell or buy then
			local right
			if sell and buy then
				right = format("%s %s·%s buy %s", Money(sell), GREY, COLOR_END, Money(buy))
			elseif sell then
				right = Money(sell)
			else
				right = format("buy %s", Money(buy))
			end
			AddDouble(tooltip, LABEL_VENDOR, right)
			added = added + 1
		end
	end

	-- 6. FL Sold/Day (+ deal score when >= 60)
	if IsOn(ts.showSaleRate) then
		local soldPerDay = Num(MarketField(itemID, "soldPerDay", suffix))
		local score = GetDealScore(itemID)
		local hasDeal = score and score >= DEAL_SCORE_MIN
		if soldPerDay > 0 or hasDeal then
			local right
			if hasDeal then
				right = format("%.1f %s·%s %sDeal %d%s", soldPerDay, GREY, COLOR_END, GREEN, floor(score), COLOR_END)
			else
				right = format("%.1f", soldPerDay)
			end
			AddDouble(tooltip, LABEL_SOLDPERDAY, right)
			added = added + 1
		end
	end

	-- 7. FL Inventory (this character vs. alts across the realm)
	if IsOn(ts.showInventory) then
		CollectInventory(itemID)
		-- Mail on this character has no slot in the line format, so it does not
		-- by itself make the line appear (alts' mail is folded into "alts").
		if invBags + invBank + invAH + invAlts > 0 then
			AddDouble(tooltip, LABEL_INVENTORY, format("bags %d %s·%s bank %d %s·%s AH %d %s·%s alts %d",
				floor(invBags), GREY, COLOR_END, floor(invBank), GREY, COLOR_END, floor(invAH), GREY, COLOR_END, floor(invAlts)))
			added = added + 1
		end
	end

	-- 8. FL Ledger (average buy / sell from this account's ledger)
	if IsOn(ts.showLedger) then
		local avgBuy, avgSell = GetLedgerAverages(itemID)
		if avgBuy or avgSell then
			local right
			if avgBuy and avgSell then
				right = format("avg buy %s %s·%s avg sell %s", Money(avgBuy), GREY, COLOR_END, Money(avgSell))
			elseif avgBuy then
				right = format("avg buy %s", Money(avgBuy))
			else
				right = format("avg sell %s", Money(avgSell))
			end
			AddDouble(tooltip, LABEL_LEDGER, right)
			added = added + 1
		end
	end

	-- 9. FL Last Scan (relative age, grey)
	if showMarket then
		local lastScan = Num(MarketField(itemID, "lastScan", suffix))
		if lastScan > 0 then
			AddDouble(tooltip, LABEL_LASTSCAN, format("%s%s%s", GREY, RelativeTime(time() - lastScan), COLOR_END))
			added = added + 1
		end
	end

	if added > 0 and type(tooltip.Show) == "function" then
		tooltip:Show()
	end
	return added
end

--------------------------------------------------------------------------------
-- Tooltip hook plumbing
--------------------------------------------------------------------------------

-- Resolve the displayed item: TooltipUtil.GetDisplayedItem → tooltip:GetItem()
-- → tooltipData.id. Returns itemID, link (link may be nil).
local function GetTooltipItem(tooltip, tooltipData)
	local link, id
	local util = TooltipUtil or _G.TooltipUtil
	if util and type(util.GetDisplayedItem) == "function" then
		local ok, _, l, i = pcall(util.GetDisplayedItem, tooltip)
		if ok then
			link, id = l, i
		end
	end
	if not link and type(tooltip.GetItem) == "function" then
		local ok, _, l = pcall(tooltip.GetItem, tooltip)
		if ok and type(l) == "string" then
			link = l
		end
	end
	if type(link) ~= "string" then
		link = nil
	end
	if not id and link then
		id = FL.ItemIDFromLink(link)
	end
	if not id and type(tooltipData) == "table" then
		id = tooltipData.id
	end
	id = tonumber(id)
	if not id or id <= 0 then
		return nil, nil
	end
	return id, link
end

-- Shared path for both hook styles: settings gates, modifier gate, the
-- double-processing guard, then AddLines under pcall (one warning per session).
local function ProcessTooltip(tooltip, itemID, link)
	local ts = TooltipSettings()
	if not ts or not IsOn(ts.enabled) then
		return
	end
	if ts.modifierOnly and not (IsShiftKeyDown and IsShiftKeyDown()) then
		return
	end
	local tick = FL.FrameTick or GetTime()
	if tooltip == lastTooltip and itemID == lastItemID and tick == lastTick then
		return
	end
	lastTooltip, lastItemID, lastTick = tooltip, itemID, tick
	local suffix = 0
	if link then
		suffix = tonumber(FL.ItemSuffixFromLink(link)) or 0
	end
	local ok, err = pcall(Tooltip.AddLines, tooltip, itemID, suffix)
	if not ok and not warnedError then
		warnedError = true
		FL:Warn("Tooltip annotation error (further errors suppressed): %s", tostring(err))
	end
end

-- TooltipDataProcessor post-call for Enum.TooltipDataType.Item.
local function OnTooltipItem(tooltip, tooltipData)
	if not tooltip then
		return
	end
	if tooltip.IsForbidden and tooltip:IsForbidden() then
		return
	end
	local name = type(tooltip.GetName) == "function" and tooltip:GetName() or nil
	if not name or not ALLOWED_TOOLTIPS[name] then
		return
	end
	local itemID, link = GetTooltipItem(tooltip, tooltipData)
	if not itemID then
		return
	end
	ProcessTooltip(tooltip, itemID, link)
end

-- Legacy OnTooltipSetItem script hook (clients without TooltipDataProcessor).
local function OnTooltipSetItemLegacy(tooltip)
	if not tooltip then
		return
	end
	if tooltip.IsForbidden and tooltip:IsForbidden() then
		return
	end
	local itemID, link = GetTooltipItem(tooltip, nil)
	if not itemID then
		return
	end
	ProcessTooltip(tooltip, itemID, link)
end

-- Install the item-tooltip hook once; returns true when some hook is active.
local function InstallHooks()
	if installed then
		return true
	end
	local tdp = TooltipDataProcessor or _G.TooltipDataProcessor
	if tdp and type(tdp.AddTooltipPostCall) == "function" then
		local enumRoot = Enum or _G.Enum
		local itemType = enumRoot and enumRoot.TooltipDataType and enumRoot.TooltipDataType.Item
		if itemType == nil then
			itemType = 0
		end
		local ok = pcall(tdp.AddTooltipPostCall, itemType, OnTooltipItem)
		if ok then
			installed = true
			installMode = "processor"
			return true
		end
	end
	local hooked = 0
	for i = 1, #TOOLTIP_NAMES do
		local tt = _G[TOOLTIP_NAMES[i]]
		if tt and type(tt.HasScript) == "function" and type(tt.HookScript) == "function" then
			local okHas, has = pcall(tt.HasScript, tt, "OnTooltipSetItem")
			if okHas and has then
				local ok = pcall(tt.HookScript, tt, "OnTooltipSetItem", OnTooltipSetItemLegacy)
				if ok then
					hooked = hooked + 1
				end
			end
		end
	end
	if hooked > 0 then
		installed = true
		installMode = "legacy"
		return true
	end
	return false
end

--------------------------------------------------------------------------------
-- Modifier refresh (modifierOnly mode)
--------------------------------------------------------------------------------

-- When modifierOnly is on, re-set the visible GameTooltip as Shift changes so
-- the lines appear/disappear without moving the mouse. Only owners that expose
-- UpdateTooltip (container/bank/merchant/AH buttons) can be refreshed.
local function OnModifierStateChanged(event, key, down)
	local ts = TooltipSettings()
	if not ts or not ts.modifierOnly or not IsOn(ts.enabled) then
		return
	end
	if type(key) ~= "string" or not strfind(key, "SHIFT", 1, true) then
		return
	end
	local gt = GameTooltip or _G.GameTooltip
	if not gt or (gt.IsForbidden and gt:IsForbidden()) then
		return
	end
	if type(gt.IsShown) ~= "function" or not gt:IsShown() then
		return
	end
	-- Allow the same tooltip+item to be processed again this frame.
	lastTick = -1
	local owner = type(gt.GetOwner) == "function" and gt:GetOwner() or nil
	if owner and type(owner.UpdateTooltip) == "function" then
		pcall(owner.UpdateTooltip, owner)
	end
end

--------------------------------------------------------------------------------
-- Public: settings hook
--------------------------------------------------------------------------------

-- Settings-change hook: resets the double-processing guard so the next tooltip
-- re-renders with the new toggles; (re)installs the hook if it is not active.
function Tooltip.Refresh()
	lastTooltip, lastItemID, lastTick = nil, nil, -1
	if not installed then
		InstallHooks()
	end
end

--------------------------------------------------------------------------------
-- Registration
--------------------------------------------------------------------------------
InstallHooks()

if type(FL.RegisterEvent) == "function" then
	FL.RegisterEvent("PLAYER_LOGIN", function()
		if not installed then
			InstallHooks()
		end
	end)
	FL.RegisterEvent("MODIFIER_STATE_CHANGED", OnModifierStateChanged)
end

if type(FL.On) == "function" then
	FL.On("FL_SETTINGS_CHANGED", function()
		Tooltip.Refresh()
	end)
	FL.On("FL_DB_READY", function()
		if not installed then
			InstallHooks()
		end
		if installed then
			FL:Debug("Tooltips: item tooltip hook active (%s mode).", installMode)
		else
			FL:Warn("Tooltips: no tooltip hook available on this client; item annotations are disabled.")
		end
	end)
end
