-- Probe: display panels driven by a circuit. Which message shows (several conditions true?),
-- how fast it follows the wire, wildcard icons, and the blueprint format. Writes
-- ticky/panel.txt.
local s, f, k, panels, log = nil, nil, nil, {}, {}
local W = defines.wire_connector_id
local V = {type = "virtual", name = "signal-V"}
local function cond(cmp, c) return {first_signal = V, comparator = cmp, constant = c} end
local function panel(x, msgs, always)
  local p = s.create_entity{name = "display-panel", position = {x, 0}, force = f}
  k.get_wire_connector(W.circuit_red, true).connect_to(p.get_wire_connector(W.circuit_red, true))
  p.get_control_behavior().messages = msgs
  if always ~= nil then p.display_panel_always_show = always end
  panels[#panels + 1] = p
end
script.on_event(defines.events.on_tick, function(e)
  if e.tick == 1 then
    s = game.surfaces[1]
    f = game.forces.player
    s.create_entity{name = "electric-energy-interface", position = {-6, 6}, force = f}
    for px = -2, 40, 14 do s.create_entity{name = "substation", position = {px, 4}, force = f} end
    k = s.create_entity{name = "constant-combinator", position = {-3, 0}, force = f}
    local check = {type = "virtual", name = "signal-check"}
    local alert = {type = "virtual", name = "signal-alert"}
    -- 1: one message per value; 2: overlapping conditions; 3: wildcard icons; 4: always show.
    panel(0, {{text = "one", icon = check, condition = cond("=", 1)}, {text = "two", icon = alert, condition = cond("=", 2)}})
    panel(2, {{text = "big", icon = check, condition = cond(">", 1)}, {text = "pos", icon = alert, condition = cond(">", 0)}})
    panel(4, {{text = "each", icon = {type = "virtual", name = "signal-each"}, condition = cond(">", 0)}})
    panel(6, {{text = "anything", icon = {type = "virtual", name = "signal-anything"}, condition = cond(">", 0)}})
    panel(8, {{text = "everything", icon = {type = "virtual", name = "signal-everything"}, condition = cond(">", 0)}})
    panel(10, {{text = "", icon = check, condition = cond("=", 1)}}, true)
    panel(12, {{text = "no icon", condition = cond("=", 1)}}, true)
    panels[1].display_panel_show_in_chart = true
  elseif e.tick >= 2 and e.tick <= 12 then
    local v = ({[2] = 0, [3] = 1, [4] = 1, [5] = 2, [6] = 2, [7] = 3, [8] = 0, [9] = 1, [10] = 1, [11] = 1, [12] = 1})[e.tick]
    local sec = k.get_control_behavior().get_section(1)
    sec.set_slot(1, {value = {type = "virtual", name = "signal-V", quality = "normal"}, min = v})
    sec.set_slot(2, {value = {type = "item", name = "iron-plate", quality = "normal"}, min = 5})
    local row = {"tick " .. e.tick .. " set V=" .. v .. ":"}
    for i, p in ipairs(panels) do
      local ic = p.display_panel_icon
      row[#row + 1] = i .. "=" .. tostring(p.display_panel_text) .. "/" .. (ic and ic.name or "-")
    end
    log[#log + 1] = table.concat(row, " ")
  elseif e.tick == 13 then
    local inv = game.create_inventory(1)
    inv.insert{name = "blueprint"}
    local bp = inv[1]
    bp.create_blueprint{surface = s, force = f, area = {{-4, -2}, {14, 2}}}
    for _, ent in ipairs(bp.get_blueprint_entities() or {}) do
      if ent.name == "display-panel" then
        log[#log + 1] = "bp: " .. helpers.table_to_json(ent)
      end
    end
    helpers.write_file("ticky/panel.txt", table.concat(log, "\n") .. "\n")
    helpers.write_file("ticky/done.txt", "ok")
  end
end)
