-- Probe: checks combinator semantics the compiler relies on. Writes ticky/probe.txt.
local out = {}
local function log(s) out[#out + 1] = s end
local V = function(n, q) return {type = "virtual", name = n, quality = q} end
local I = function(n, q) return {type = "item", name = n, quality = q} end
local EACH, EVERY = V("signal-each"), V("signal-everything")
local RED, GREEN = {red = true, green = false}, {red = false, green = true}

local s, f
local x = 0
local function konst(vals)
  x = x + 4
  local c = s.create_entity{name = "constant-combinator", position = {x, 0}, force = f}
  local sec = c.get_control_behavior().get_section(1)
  for i, v in ipairs(vals) do sec.set_slot(i, {value = {type = v[1].type, name = v[1].name, quality = v[1].quality or "normal"}, min = v[2]}) end
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
    s = game.create_surface("p", {width = 2048, height = 64})
    s.generate_with_lab_tiles = true
    s.request_to_generate_chunks({0, 0}, 12)
    s.force_generate_chunk_requests()
    f = game.forces.player
    s.create_entity{name = "electric-energy-interface", position = {-6, 6}, force = f}
    for px = -2, 1000, 14 do s.create_entity{name = "substation", position = {px, 4}, force = f} end
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
    -- Level 4: signal arrays.
    local arr = {{I("iron-plate"), 5}, {I("copper-plate"), -3}, {I("coal"), 9}}
    local K = {{I("iron-plate"), 1}, {I("copper-plate"), 2}, {I("coal"), 3}}
    local KI = {{I("iron-plate"), 1}, {I("copper-plate"), 2}, {I("coal"), 3}, {V("signal-I"), 2}}
    t("L1 read: each(green)=I(green) -> X copy red", "decider-combinator",
      {conditions = {{first_signal = EACH, first_signal_networks = GREEN, second_signal = V("signal-I"), second_signal_networks = GREEN, comparator = "="}},
       outputs = {{signal = V("signal-X"), copy_count_from_input = true, networks = RED}}}, arr, KI)
    t("L2 onehot: each(red)=I(green) -> each 1", "decider-combinator",
      {conditions = {{first_signal = EACH, first_signal_networks = RED, second_signal = V("signal-I"), second_signal_networks = GREEN, comparator = "="}},
       outputs = {{signal = EACH, copy_count_from_input = false, constant = 1}}}, K, {{V("signal-I"), 2}})
    t("L3 mask: each(red)!=0 and each(green)=0 -> each copy red", "decider-combinator",
      {conditions = {{first_signal = EACH, first_signal_networks = RED, constant = 0, comparator = "≠"},
        {first_signal = EACH, first_signal_networks = GREEN, constant = 0, comparator = "=", compare_type = "and"}},
       outputs = {{signal = EACH, copy_count_from_input = true, networks = RED}}}, arr, {{I("copper-plate"), 1}})
    -- Bundle comparisons (`a < b`): `each` on both sides of one decider condition.
    local za = {{I("iron-plate"), 5}, {I("copper-plate"), 3}, {I("coal"), -7}, {I("stone"), 7}}
    local zb = {{I("iron-plate"), 5}, {I("copper-plate"), 9}, {I("coal"), 2}, {I("wood"), -1}}
    local okz, errz = pcall(function()
      t("Z1 each(red) < each(green) -> each 1", "decider-combinator",
        {conditions = {{first_signal = EACH, first_signal_networks = RED, second_signal = EACH, second_signal_networks = GREEN, comparator = "<"}},
         outputs = {{signal = EACH, copy_count_from_input = false, constant = 1}}}, za, zb)
      t("Z2 each(red) >= each(green) -> each 1", "decider-combinator",
        {conditions = {{first_signal = EACH, first_signal_networks = RED, second_signal = EACH, second_signal_networks = GREEN, comparator = "≥"}},
         outputs = {{signal = EACH, copy_count_from_input = false, constant = 1}}}, za, zb)
    end)
    if not okz then log("Z error: " .. tostring(errz)) end
    t("L4 each >> 1 -> X (single -5)", "arithmetic-combinator",
      {first_signal = EACH, first_signal_networks = RED, second_constant = 1, operation = ">>", output_signal = V("signal-X")}, {{I("iron-plate"), -5}}, nil)
    t("L5 each >> 1 -> X (7, -5)", "arithmetic-combinator",
      {first_signal = EACH, first_signal_networks = RED, second_constant = 1, operation = ">>", output_signal = V("signal-X")}, {{I("iron-plate"), 7}, {I("copper-plate"), -5}}, nil)
    local ties = {{I("iron-plate"), 3}, {I("copper-plate"), 3}, {I("coal"), 1}, {I("stone"), -7}}
    for k = 0, 3 do
      t("L6 select max index " .. k, "selector-combinator", {operation = "select", select_max = true, index_constant = k}, ties, nil)
      t("L7 select min index " .. k, "selector-combinator", {operation = "select", select_max = false, index_constant = k}, ties, nil)
    end
    t("L8 select max index 9 (out of range)", "selector-combinator", {operation = "select", select_max = true, index_constant = 9}, ties, nil)
    t("L9 selector red+green summed", "selector-combinator", {operation = "select", select_max = true, index_constant = 0}, {{I("iron-plate"), 3}}, {{I("iron-plate"), 4}, {I("coal"), 5}})
    -- Quality variants as separate signals (needs the Quality mod).
    if prototypes.quality["uncommon"] then
      local mix = {{V("signal-A"), 5}, {V("signal-A", "uncommon"), 7}, {I("iron-plate", "uncommon"), 3}, {V("signal-A", "legendary"), -2}}
      t("Q1 each(red)+0 -> each", "arithmetic-combinator",
        {first_signal = EACH, first_signal_networks = RED, second_constant = 0, operation = "+", output_signal = EACH}, mix, nil)
      t("Q2 each(red)>4 -> each copy", "decider-combinator",
        {conditions = {{first_signal = EACH, first_signal_networks = RED, constant = 4, comparator = ">"}},
         outputs = {{signal = EACH, copy_count_from_input = true, networks = RED}}}, mix, nil)
      t("Q3 A@uncommon(red)=7 -> X@rare=1", "decider-combinator",
        {conditions = {{first_signal = V("signal-A", "uncommon"), first_signal_networks = RED, constant = 7, comparator = "="}},
         outputs = {{signal = V("signal-X", "rare"), copy_count_from_input = false, constant = 1}}}, mix, nil)
      t("Q3b A@normal(red)=7 -> X=1 (expect none)", "decider-combinator",
        {conditions = {{first_signal = V("signal-A"), first_signal_networks = RED, constant = 7, comparator = "="}},
         outputs = {{signal = V("signal-X"), copy_count_from_input = false, constant = 1}}}, mix, nil)
      t("Q4 A@uncommon * 2 -> B@epic", "arithmetic-combinator",
        {first_signal = V("signal-A", "uncommon"), first_signal_networks = RED, second_constant = 2, operation = "*", output_signal = V("signal-B", "epic")}, mix, nil)
      t("Q4b A@uncommon(red) + A@legendary(green) -> C@rare", "arithmetic-combinator",
        {first_signal = V("signal-A", "uncommon"), first_signal_networks = RED, second_signal = V("signal-A", "legendary"), second_signal_networks = GREEN, operation = "+", output_signal = V("signal-C", "rare")}, mix, {{V("signal-A", "legendary"), 100}})
      for k = 0, 3 do
        t("Q5 select max index " .. k, "selector-combinator", {operation = "select", select_max = true, index_constant = k}, mix, nil)
      end
      t("Q6 selector count", "selector-combinator", {operation = "count", count_signal = V("signal-X", "epic")}, mix, nil)
      t("Q7 everything copy", "decider-combinator",
        {conditions = {{first_signal = V("signal-check"), first_signal_networks = GREEN, constant = 0, comparator = "≠"}},
         outputs = {{signal = EVERY, copy_count_from_input = true, networks = RED}}}, mix, {{V("signal-check"), 1}})
      t("Q8 each(red)+each(green)", "arithmetic-combinator",
        {first_signal = EACH, first_signal_networks = RED, second_signal = EACH, second_signal_networks = GREEN, operation = "+", output_signal = EACH},
        mix, {{V("signal-A"), 1}, {V("signal-A", "uncommon"), 10}, {V("signal-A", "rare"), 100}})
      t("Q9 each(red)+0 -> X@rare (sum)", "arithmetic-combinator",
        {first_signal = EACH, first_signal_networks = RED, second_constant = 0, operation = "+", output_signal = V("signal-X", "rare")}, mix, nil)
      t("Q10 read: each(green)=I@rare(green) -> X@epic copy red", "decider-combinator",
        {conditions = {{first_signal = EACH, first_signal_networks = GREEN, second_signal = V("signal-I", "rare"), second_signal_networks = GREEN, comparator = "="}},
         outputs = {{signal = V("signal-X", "epic"), copy_count_from_input = true, networks = RED}}},
        {{V("signal-A", "uncommon"), 11}, {V("signal-B", "uncommon"), 22}, {V("signal-A", "rare"), 33}},
        {{V("signal-A", "uncommon"), 1}, {V("signal-B", "uncommon"), 2}, {V("signal-A", "rare"), 3}, {V("signal-I", "rare"), 3}})
    else
      log("Q: no quality prototypes")
    end
  end
  if e.tick == 12 then
    for _, tc in ipairs(tests) do
      local cb = tc[2].get_control_behavior()
      local parts = {}
      for _, sg in pairs(cb.signals_last_tick or {}) do
        local q = sg.signal.quality
        if type(q) ~= "string" and q then q = q.name end
        parts[#parts + 1] = sg.signal.name .. ((q and q ~= "normal") and ("@" .. q) or "") .. "=" .. sg.count
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
