local terms = require './terms'

function test_levels()
  local test_term = terms.inferrable.level_max(terms.inferrable.level_suc(terms.inferrable.level0), terms.inferrable.level0)
  local inferred_type, inferred_term = terms.infer(test_term, {})
  p(inferred_type)
  assert(inferred_type.kind == "value_level_type")
  local result = terms.evaluate(inferred_term, {})
  p(result)
  assert(result.kind == "value_level")
  assert(result.level == 1)
end

function test_star()
  local test_term = terms.inferrable.star
  local inferred_type, inferred_term = terms.infer(test_term, {})
  p(inferred_type, inferred_term)
  assert(inferred_type.kind == "value_star")
  local result = terms.evaluate(inferred_term, {})
  p(result)
  assert(result.kind == "value_star")
  assert(result.level == 0)
end

function test_metavariable_bind_to_other_mv()
  local tcs = terms.typechecker_state()
  local mv_a = tcs:metavariable()
  local mv_b = tcs:metavariable()
  mv_a:bind_metavariable(mv_a) -- noop
  mv_b:bind_metavariable(mv_a) -- mv_b binds to mv_a
  local canonical_a = mv_a:get_canonical()
  local canonical_b = mv_b:get_canonical()
  p(mv_a, mv_b, canonical_a, canonical_b)
  assert(mv_b:get_canonical().id == mv_a.id)
  local mv_c = tcs:metavariable()
  mv_c:bind_metavariable(mv_b)
  assert(mv_c:get_canonical().id == mv_a.id)
  -- check that bound ID was correctly collapsed
  assert(tcs.mvs[mv_c.id].bound_mv_id == mv_a.id)
end

test_levels()
test_star()
test_metavariable_bind_to_other_mv()
