# ForeverLedger

A monolithic auction-house and economy addon for **World of Warcraft: Forever** (Patch 1.60.1, Interface 16001,
game type `camelot`). It combines a TradeSkillMaster-style relational market database and formula pricing engine with an
Auctionator-style scanning and posting workflow, then adds a real-time sniper, one-click undercut posting, a crafting
restock queue, cross-character inventory, a sales ledger and market intelligence.

## Install

1. Copy the `ForeverLedger` folder to `World of Warcraft\_classic_beta_\Interface\AddOns\`.
2. Provide AceGUI-3.0 (see `Libs\README.txt`): either install the standalone **Ace3** addon (WoW Forever flavour) or
   copy `CallbackHandler-1.0` and `AceGUI-3.0` into `ForeverLedger\Libs\`.
3. Restart the client fully (Forever does not always pick up new addon folders on `/reload`).

## Commands

| Command | Action |
| --- | --- |
| `/fl` or `/fledger` | Toggle the dashboard |
| `/fl scan` | Full auction-house scan (`C_AuctionHouse.ReplicateItems`, 15-minute cooldown) |
| `/fl scan <itemLink or itemID>` | Scan one item's price ladder |
| `/fl snipe on` / `off` | Start or stop the sniper loop (AH must be open) |
| `/fl post` | Build the posting queue from your bags |
| `/fl queue` | Build the crafting restock queue |
| `/fl price <formula> [itemID]` | Evaluate a pricing formula |
| `/fl export` / `/fl import <string>` | Export or import your database as text |
| `/fl save` | Write the in-memory database to SavedVariables now |
| `/fl help` | List commands |

## WoW Forever cold-start safeguard

Early Forever beta builds (before 70009) wrote SavedVariables on logout but failed to load them on a cold client start,
and the next logout overwrote the good file with an empty database. ForeverLedger keeps the whole database in an
in-memory runtime copy, writes it back to **two** SavedVariables files (account-wide and per-character) with a
generation counter, hydrates from whichever copy is newest, warns you in chat when it finds an empty database on a
cold start, and lets you keep an out-of-game backup with `/fl export`.

## Pricing formulas

TSM-compatible syntax: `min(dbmarket, 150% crafting, 200g)`, `max(vendorsell * 1.5, crafting * 1.05)`,
`ifgt(dbsalerate, 2, dbmarket, dbminbuyout)`. Sources: `dbmarket`, `dbminbuyout`, `dbhistorical`, `numauctions`,
`dbsalerate`, `crafting`, `vendorsell`, `vendorbuy`, `matprice`, `avgbuy`, `avgsell`, `inventory`, `undercut`,
`postmin`, `postmax`, `restocktarget`. Money literals `1g2s3c`, percentages `150%`.

## Hardware-event compliance

Buying, confirming, posting and cancelling go through `SecureActionButtonTemplate` buttons that you physically click
(`ForeverLedgerSecureBuy`, `ForeverLedgerSecurePost`, `ForeverLedgerSecureCancel`). The addon arms the button with the
next action and label; your click executes it inside a genuine hardware event, as the client requires.
