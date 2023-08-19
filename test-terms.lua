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

function test_unify()
  local tcs = terms.typechecker_state()

  local mv_a = tcs:metavariable()
  local free_mv_a = terms.types.value.free.metavariable(mv_a)
  p(mv_a, free_mv_a)

  local unified = terms.unify(free_mv_a, terms.types.value.level_type)
  assert(unified == terms.types.value.level_type)
  assert(mv_a:get_value() == terms.types.value.level_type)
end

function test_unify_more_metavariables()
  local tcs = terms.typechecker_state()

  -- terms.types.value.free.metavariable(...)
  -- terms.types.value.free.axiom(...)
  -- VS
  -- terms.types.value.free(terms.free.metavariable(...))

  local mv_a = tcs:metavariable()
  local mv_b = tcs:metavariable()
  p('mv_a', mv_a)
  local free_mv_a = terms.types.value.free.metavariable(mv_a)
  local free_mv_b = terms.types.value.free.metavariable(mv_b)
  p(mv_a, free_mv_a)

  terms.unify(free_mv_b, free_mv_a)
  assert(mv_b:get_canonical().id == mv_a.id)

  local unified = terms.unify(free_mv_a, terms.types.value.level_type)
  assert(unified == terms.types.value.level_type)
  assert(mv_a:get_value() == terms.types.value.level_type)

  assert(mv_b:get_value() == terms.types.value.level_type)
end

function test_unify_2()
  local level_type = terms.types.value.level_type
  local prim = terms.types.value.prim
  --local unified_1 = terms.unify(level_type, prim)
  -- TODO: how to test that a lua error correctly happens?

  local tcs = terms.typechecker_state()
  local mv_a = tcs:metavariable()
  local mv_b = tcs:metavariable()
  local resultinfo = function(x) return terms.types.value.resultinfo(terms.types.resultinfo(x)) end
  local freemeta = terms.types.value.free.metavariable
  local resinfo_a = resultinfo(freemeta(mv_a))
  local resinfo_b = resultinfo(freemeta(mv_b))
  local resinfo_effectful = resultinfo(terms.types.purity.effectful)
  local resinfo_pure = resultinfo(terms.types.purity.pure)
  local unified_2 = terms.unify(resinfo_a, resinfo_effectful)
  p(unified_2, mv_a)
  assert(unified_2 == resinfo_effectful)
  --local unified_3 = terms.unify(resinfo_a, resinfo_pure)
end


test_levels()
test_star()
test_metavariable_bind_to_other_mv()
test_unify()
test_unify_more_metavariables()
test_unify_2()
