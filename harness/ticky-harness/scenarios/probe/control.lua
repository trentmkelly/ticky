-- Probe: checks combinator semantics the compiler relies on. Writes ticky/probe.txt.
local out = {}
local function log(s) out[#out + 1] = s end
local V = function(n) return {type = "virtual", name = n} end
local I = function(n) return {type = "item", name = n} end
local EACH, EVERY = V("signal-each"), V("signal-everything")
local RED, GREEN = {red = true, green = false}, {red = false, green = true}

local s, f
local x = 0
local function konst(vals)
  x = x + 4
  local c = s.create_entity{name = "constant-combinator", position = {x, 0}, force = f}
  local sec = c.get_control_behavior().get_section(1)
  for i, v in ipairs(vals) do sec.set_slot(i, {value = {type = v[1].type, name = v[1].name, quality = "normal"}, min = v[2]}) end
  return c
end
local function comb(name)
  x = x + 4
  return s.create_entity{name = name, position = {x, 0}, force = f}
end
local function wire(a, ac, b, bc)
  a.get_wire_connector(ac, true).connect_to(b.get_wire_connector(bc, true))
end
local W = defines.wire_connector_id
-- A combinator fed by `red` on its red input and `green` on its green input.
local function probe(name, params, red, green)
  local c = comb(name)
  c.get_control_behavior().parameters = params
  if red then wire(konst(red), W.circuit_red, c, W.combinator_input_red) end
  if green then wire(konst(green), W.circuit_green, c, W.combinator_input_green) end
  return c
end

local tests = {}
local function t(label, name, params, red, green) tests[#tests + 1] = {label, probe(name, params, red, green)} end

script.on_event(defines.events.on_tick, function(e)
  if e.tick == 1 then
    s = game.create_surface("p", {width = 1024, height = 64})
    s.generate_with_lab_tiles = true
    s.request_to_generate_chunks({0, 0}, 12)
    s.force_generate_chunk_requests()
    f = game.forces.player
    s.create_entity{name = "electric-energy-interface", position = {-6, 6}, force = f}
    for px = -2, 600, 14 do s.create_entity{name = "substation", position = {px, 4}, force = f} end
    local bundle = {{I("iron-plate"), 5}, {I("copper-plate"), -3}, {V("signal-check"), 7}, {V("signal-A"), 100}}
    local scal = {{V("signal-A"), 2}, {V("signal-check"), 1}}
    t("P1 each(red)*A(green)->each", "arithmetic-combinator",
      {first_signal = EACH, first_signal_networks = RED, second_signal = V("signal-A"), second_signal_networks = GREEN,
       operation = "*", output_signal = EACH}, bundle, scal)
    t("P2 each(red)>0 and each(red)<50 and A(green)=2 -> each copy red", "decider-combinator",
      {conditions = {{first_signal = EACH, first_signal_networks = RED, constant = 0, comparator = ">"},
        {first_signal = EACH, first_signal_networks = RED, constant = 50, comparator = "<", compare_type = "and"},
        {first_signal = V("signal-A"), first_signal_networks = GREEN, constant = 2, comparator = "=", compare_type = "and"}},
       outputs = {{signal = EACH, copy_count_from_input = true, networks = RED}}}, bundle, scal)
    t("P3a each(red)!=0 -> X=1 (count)", "decider-combinator",
      {conditions = {{first_signal = EACH, first_signal_networks = RED, constant = 0, comparator = "≠"}},
       outputs = {{signal = V("signal-X"), copy_count_from_input = false, constant = 1}}}, bundle, scal)
    t("P3b each(red)>0 -> X copy (red)", "decider-combinator",
      {conditions = {{first_signal = EACH, first_signal_networks = RED, constant = 0, comparator = ">"}},
       outputs = {{signal = V("signal-X"), copy_count_from_input = true, networks = RED}}}, bundle, scal)
    t("P4 check(green)!=0 -> everything copy red", "decider-combinator",
      {conditions = {{first_signal = V("signal-check"), first_signal_networks = GREEN, constant = 0, comparator = "≠"}},
       outputs = {{signal = EVERY, copy_count_from_input = true, networks = RED}}}, bundle, scal)
    t("P5 each(red)+0 -> X", "arithmetic-combinator",
      {first_signal = EACH, first_signal_networks = RED, second_constant = 0, operation = "+", output_signal = V("signal-X")}, bundle, scal)
    t("P6 selector max", "selector-combinator", {operation = "select", select_max = true, index_constant = 0}, bundle, nil)
    t("P6b selector min", "selector-combinator", {operation = "select", select_max = false, index_constant = 0}, bundle, nil)
    t("P6c selector count", "selector-combinator", {operation = "count", count_signal = V("signal-X")}, bundle, nil)
    local ok, err = pcall(function()
      t("P7 each(red)*each(green)->each", "arithmetic-combinator",
        {first_signal = EACH, first_signal_networks = RED, second_signal = EACH, second_signal_networks = GREEN,
         operation = "*", output_signal = EACH}, bundle, {{I("iron-plate"), 3}, {V("signal-A"), 2}})
    end)
    if not ok then log("P7 error: " .. tostring(err)) end
    t("P8 each(red)>0 -> each = 5", "decider-combinator",
      {conditions = {{first_signal = EACH, first_signal_networks = RED, constant = 0, comparator = ">"}},
       outputs = {{signal = EACH, copy_count_from_input = false, constant = 5}}}, bundle, scal)
    local ok9, err9 = pcall(function()
      t("P9 10 - each(red) -> each", "arithmetic-combinator",
        {first_constant = 10, second_signal = EACH, second_signal_networks = RED, operation = "-", output_signal = EACH}, bundle, scal)
    end)
    if not ok9 then log("P9 error: " .. tostring(err9)) end
    t("P10 each(red) < A(green) -> each copy red", "decider-combinator",
      {conditions = {{first_signal = EACH, first_signal_networks = RED, second_signal = V("signal-A"), second_signal_networks = GREEN, comparator = "<"}},
       outputs = {{signal = EACH, copy_count_from_input = true, networks = RED}}}, bundle, scal)
    t("P12 each(red)+each(green)->each", "arithmetic-combinator",
      {first_signal = EACH, first_signal_networks = RED, second_signal = EACH, second_signal_networks = GREEN,
       operation = "+", output_signal = EACH}, bundle, {{I("iron-plate"), 3}, {V("signal-B"), 2}})
    t("P13 each(red)//each(green)->each", "arithmetic-combinator",
      {first_signal = EACH, first_signal_networks = RED, second_signal = EACH, second_signal_networks = GREEN,
       operation = "/", output_signal = EACH}, bundle, {{I("iron-plate"), 2}, {V("signal-B"), 2}})
    t("P14 each(both)+0 -> each, red+green same signal", "arithmetic-combinator",
      {first_signal = EACH, second_constant = 0, operation = "+", output_signal = EACH}, bundle, {{I("iron-plate"), 3}})
    t("P15 everything(red)>0 -> X=1", "decider-combinator",
      {conditions = {{first_signal = EVERY, first_signal_networks = RED, constant = -10, comparator = ">"}},
       outputs = {{signal = V("signal-X"), copy_count_from_input = false, constant = 1}}}, bundle, scal)
    t("P11 each(red) < A(red)", "decider-combinator",
      {conditions = {{first_signal = EACH, first_signal_networks = RED, second_signal = V("signal-A"), second_signal_networks = RED, comparator = "<"}},
       outputs = {{signal = EACH, copy_count_from_input = true, networks = RED}}}, bundle, scal)
  end
  if e.tick == 12 then
    for _, tc in ipairs(tests) do
      local cb = tc[2].get_control_behavior()
      local parts = {}
      for _, sg in pairs(cb.signals_last_tick or {}) do
        parts[#parts + 1] = sg.signal.name .. "=" .. sg.count
      end
      table.sort(parts)
      log(tc[1] .. ": " .. table.concat(parts, " "))
    end
    -- Blueprint JSON of the whole probe area.
    local inv = game.create_inventory(1)
    inv[1].set_stack{name = "blueprint"}
    inv[1].create_blueprint{surface = s, force = f, area = {{-2, -4}, {x + 4, 4}}}
    helpers.write_file("ticky/probe-bp.txt", inv[1].export_stack())
    helpers.write_file("ticky/probe.txt", table.concat(out, "\n") .. "\n")
    helpers.write_file("ticky/done.txt", "ok")
  end
end)
