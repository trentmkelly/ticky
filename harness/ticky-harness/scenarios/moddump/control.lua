-- Writes ticky/moddump.tsv: every item, fluid and recipe with the mod that created it
-- (one per line: type, name, creating mod, JSON of localised_name, and for recipes the
-- category plus JSON ingredients/products). Filtered and resolved to text outside the game.
local function stacks(list)
  local out = {}
  for _, x in ipairs(list or {}) do
    out[#out + 1] = {type = x.type, name = x.name, amount = x.amount, min = x.amount_min,
      max = x.amount_max, p = x.probability}
  end
  return out
end
script.on_event(defines.events.on_tick, function(e)
  if e.tick ~= 1 then return end
  local rows = {}
  for _, kind in ipairs({"item", "fluid", "recipe"}) do
    for name, proto in pairs(prototypes[kind]) do
      local ok, h = pcall(prototypes.get_history, proto.type, name)
      if not ok then h = nil end
      local row = {kind, name, h and h.created or "?", helpers.table_to_json({proto.localised_name})}
      if kind == "recipe" then
        row[#row + 1] = proto.category
        row[#row + 1] = helpers.table_to_json({stacks(proto.ingredients)})
        row[#row + 1] = helpers.table_to_json({stacks(proto.products)})
        row[#row + 1] = tostring(proto.energy)
      end
      rows[#rows + 1] = table.concat(row, "\t")
    end
  end
  helpers.write_file("ticky/moddump.tsv", table.concat(rows, "\n") .. "\n")
  helpers.write_file("ticky/done.txt", "ok")
end)
