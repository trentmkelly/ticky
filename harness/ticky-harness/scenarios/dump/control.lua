-- Dumps every signal the game knows (items, fluids, virtual signals, recipes, qualities, space
-- locations, asteroid chunks) to ticky/signals.tsv, in the format of data/signals.tsv.
script.on_event(defines.events.on_tick, function(e)
  if e.tick ~= 1 then return end
  local lines = {}
  local function add(kind, p, special)
    local sub = p.subgroup and p.subgroup.name or ""
    lines[#lines + 1] = table.concat({kind, p.name, tostring(p.hidden or false), tostring(p.parameter or false),
      tostring(special or false), p.order or "", sub}, "\t")
  end
  for _, p in pairs(prototypes.virtual_signal) do add("virtual", p, p.special) end
  for _, p in pairs(prototypes.item) do add("item", p) end
  for _, p in pairs(prototypes.fluid) do add("fluid", p) end
  for _, p in pairs(prototypes.recipe) do add("recipe", p) end
  for _, p in pairs(prototypes.quality) do add("quality", p) end
  for _, p in pairs(prototypes.space_location or {}) do add("space-location", p) end
  for _, p in pairs(prototypes.asteroid_chunk or {}) do add("asteroid-chunk", p) end
  helpers.write_file("ticky/signals.tsv", table.concat(lines, "\n") .. "\n")
  helpers.write_file("ticky/done.txt", "ok")
end)
