ForeverLedger library folder
============================

Shipped here:
  Libs\LibStub\LibStub.lua                 (public domain, included)

Required for the dashboard GUI (not redistributed in this bundle):
  Libs\CallbackHandler-1.0\CallbackHandler-1.0.xml  (+ CallbackHandler-1.0.lua)
  Libs\AceGUI-3.0\AceGUI-3.0.xml                    (+ AceGUI-3.0.lua and the widgets\ folder)

Two ways to satisfy the dependency:

  1) Install the standalone "Ace3" addon from CurseForge (release r1403 or newer, flavour "WoW Forever").
     ForeverLedger declares "## OptionalDeps: Ace3" so Ace3 loads first and LibStub("AceGUI-3.0") resolves.

  2) Copy the folders "CallbackHandler-1.0" and "AceGUI-3.0" from an Ace3 release into this Libs\ folder so the
     paths referenced by embeds.xml exist. Keep the folder names exactly as above.

Everything except the AceGUI dashboard (scanning, sniper alerts and purchases, posting, crafting queue, tooltips,
ledger, slash commands) works without Ace3. If AceGUI-3.0 is missing, /fl prints a reminder instead of opening the window.
