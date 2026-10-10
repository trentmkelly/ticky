-- Dumps every item's stack size and rocket capacity as the selector combinator reports them
-- (modes `stack-size` and `rocket-capacity`) to ticky/items.tsv: name, stack size, rocket
-- capacity (0 when the selector drops the item).
local s, f, sels, names
local W = defines.wire_connector_id
local function pair(mode, x, list)
  local k = s.create_entity{name = "constant-combinator", position = {x, 0}, force = f}
  local cb = k.get_control_behavior()
  local sec = cb.get_section(1)
  local i = 0
  for _, n in ipairs(list) do
    i = i + 1
    if i > 1000 then sec = cb.add_section(); i = 1 end
    sec.set_slot(i, {value = {type = "item", name = n, quality = "normal"}, min = 1})
  end
  local c = s.create_entity{name = "selector-combinator", position = {x, 3}, force = f}
  c.get_control_behavior().parameters = {operation = mode}
  k.get_wire_connector(W.circuit_red, true).connect_to(c.get_wire_connector(W.combinator_input_red, true))
  return c
end
script.on_event(defines.events.on_tick, function(e)
  if e.tick == 1 then
    s = game.surfaces[1]
    f = game.forces.player
    s.create_entity{name = "electric-energy-interface", position = {-6, 6}, force = f}
    for px = -2, 40, 14 do s.create_entity{name = "substation", position = {px, 6}, force = f} end
    names = {}
    for n, p in pairs(prototypes.item) do
      if not p.parameter then names[#names + 1] = n end
    end
    table.sort(names)
    sels = {pair("stack-size", 0, names), pair("rocket-capacity", 4, names)}
  elseif e.tick == 5 then
    local got = {}
    for j, c in ipairs(sels) do
      got[j] = {}
      for _, sg in pairs(c.get_control_behavior().signals_last_tick or {}) do got[j][sg.signal.name] = sg.count end
    end
    local lines = {}
    for _, n in ipairs(names) do
      lines[#lines + 1] = n .. "\t" .. (got[1][n] or 0) .. "\t" .. (got[2][n] or 0)
    end
    helpers.write_file("ticky/items.tsv", table.concat(lines, "\n") .. "\n")
    helpers.write_file("ticky/done.txt", "ok")
  end
end)
