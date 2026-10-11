-- Which recipe does an assembler on "Set recipe" pick, and does its own "Read ingredients"
-- output feed back into that choice? Writes ticky/recipeprobe.txt.
local s, f, cases = nil, nil, {}
local W = defines.wire_connector_id
local function case(name, signals, read_ingredients)
  local x = #cases * 8
  local k = s.create_entity{name = "constant-combinator", position = {x, 0}, force = f}
  local sec = k.get_control_behavior().get_section(1)
  for i, sg in ipairs(signals) do
    sec.set_slot(i, {value = {type = sg[1], name = sg[2], quality = "normal"}, min = sg[3]})
  end
  local a = s.create_entity{name = "assembling-machine-3", position = {x, 4}, force = f}
  local cb = a.get_or_create_control_behavior()
  cb.circuit_set_recipe = true
  cb.circuit_read_ingredients = read_ingredients
  k.get_wire_connector(W.circuit_red, true).connect_to(a.get_wire_connector(W.circuit_red, true))
  cases[#cases + 1] = {name = name, a = a}
end
script.on_event(defines.events.on_tick, function(e)
  if e.tick == 1 then
    s = game.surfaces[1]; f = game.forces.player
    for _, t in pairs(f.technologies) do t.researched = true end
    s.create_entity{name = "electric-energy-interface", position = {-6, 10}, force = f}
    for px = -2, 80, 14 do s.create_entity{name = "substation", position = {px, 10}, force = f} end
    case("recipe copper-ore=1 alone", {{"recipe", "cube-jelly-ore-advanced-copper", 1}}, false)
    case("recipe copper-ore=1 + read ingredients", {{"recipe", "cube-jelly-ore-advanced-copper", 1}}, true)
    case("recipe copper-ore=1 + item cube-jelly=50", {{"recipe", "cube-jelly-ore-advanced-copper", 1}, {"item", "cube-jelly", 50}}, false)
    case("recipe copper-ore=1000000 + read ingredients", {{"recipe", "cube-jelly-ore-advanced-copper", 1000000}}, true)
    case("recipe metallic-aggravation=1 + read ingredients", {{"recipe", "metallic-aggravation", 1}}, true)
    case("recipe matter-amplification=1 + read ingredients", {{"recipe", "matter-amplification", 1}}, true)
  elseif e.tick == 30 then
    local out = {}
    for _, c in ipairs(cases) do
      local r = c.a.get_recipe()
      local net = c.a.get_circuit_network(W.circuit_red)
      local sigs = {}
      for _, sg in pairs(net and net.signals or {}) do sigs[#sigs + 1] = (sg.signal.type or "item") .. ":" .. sg.signal.name .. "=" .. sg.count end
      out[#out + 1] = c.name .. "  ->  " .. (r and r.name or "none") .. "   [wire: " .. table.concat(sigs, ", ") .. "]"
    end
    helpers.write_file("ticky/recipeprobe.txt", table.concat(out, "\n") .. "\n")
    helpers.write_file("ticky/done.txt", "ok")
  end
end)
