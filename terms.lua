-- provide ways to construct all terms
-- checker untyped term and typechecking context -> typed term
-- evaluator takes typed term and runtime context -> value

-- type checker monad
-- error handling and metavariable unification facilities
--
-- typechecker is allowed to fail, typechecker monad carries failures upwards
--   for now fail fast, but design should vaguely support multiple failures

-- metavariable unification
--   a metavariable is like a variable butmore meta
--   create a set of variables -> feed into code -> evaluate with respect to them
--   in order for the values produced by these two invocations to be the same, what would the metavariales need to be bound to?
--   (this is like symbolic execution)
--
-- in the typechecking monad we create a metavariable which takes a type and produces a term or value of that type and
-- we can unfy two values against each other to solve their metavariables or it can fail
-- for now unification with equality is the only kind of constraint. eventuall may be others but that's hard/no need right now

-- we will use lua errors for handling here - use if, error not assert so JIT understands
-- metavariables = table, edit the table, this is the stateful bit the monad has
-- methods on metavariable that bind equal to some value, if it is already bound it has to unify which can fail, failure cascades
-- thing passed to bind equl method on metavariable is a 'value' - enumerated datatype, like term but less cases
--   scaffolding - need to add cases here foreach new value variant
--
-- create metavariable, pass in as arg to lambda, get back result, unify against another type
--   it's ok if a metavariable never gets constrained during part of typechecking
-- give metavariables sequential ids (tracked in typechecker_state)

-- metavariable state transitions, can skip steps but must always move down

-- unbound
-- vvv
-- bound to exactly another metavariable - have a reference to a metavariable
-- vvv
-- bound to a value - have a reference to a value

-- when binding to another metavariable bind the one with a greater index to the lesser index

local free = {
  metavariable = function(metavariable)
    return {
      kind = "free_metavariable",
      metavariable = metavariable,
    }
  end
}

local function getmvinfo(id, mvs)
  if mvs == nil then
    return
  end
  -- if this is slow fixme later
  return mvs[id] or getmvinfo(id, mvs.prev_mvs)
end

local metavariable_mt

metavariable_mt = {
  __index = {
    getvalue = function(self)
      local canonical = self:getcanonical()
      local canonical_info = getmvinfo(canonical.id, self.typechecker_state.mvs)
      return canonical_info.bound_value or values.free(free.metavariable(canonical))
    end,
    get_canonical = function(self)
      local canonical_id = self.typechecker_state:get_canonical_id(self.id)

      if canonical_id ~= self.id then
        return setmetatable({
            id = canonical_id,
            typechecker_state = self.typechecker_state,
                            }, metavariable_mt):get_canonical()
      end

      return self
    end,
    bind = function(self, other)
      if getmetatable(other) == metavariable_mt then
        self:bind_metavariable(other)
      else
        self:bind_value(other)
      end
    end,
    bind_value = function(self, value)
      local canonical = self:getcanonical()
      local canonical_info = getmvinfo(canonical.id, self.typechecker_state.mvs)
      if canonical_info.bound_value and canonical_info.bound_value ~= value then
        error("metavariable already bound to a different value")
      end
      self.typechecker_state.mvs[canonical.id] = {
        bound_value = value,
      }
    end,
    bind_metavariable = function(self, other)
      if self == other then
        return
      end

      if getmetatable(other) ~= metavariable_mt then
        p(self, other, getmetatable(self), getmetatable(other))
        error("metavariable.bind should only be called with metavariable as arg")
      end

      if self.typechecker_state ~= other.typechecker_state then
        error("trying to mix metavariables from different typechecker_states")
      end

      if self.id == other.id then
        return
      end

      if self.id < other.id then
        return other:bind_metavariable(self)
      end

      local this = getmvinfo(self.id, self.typechecker_state.mvs)
      if this.bound_value then
        error("metavariable is already bound to a value")
      end

      self.typechecker_state.mvs[self.id] = {
        bound_mv_id = other.id,
      }
    end
  }
}

local typechecker_state_mt
typechecker_state_mt = {
  __index = {
    metavariable = function(self) -- -> metavariable instance
      self.next_metavariable_id = self.next_metavariable_id + 1
      self.mvs[self.next_metavariable_id] = {}
      return setmetatable(
        {
          id = self.next_metavariable_id,
          typechecker_state = self,
        }, metavariable_mt)
    end,
    get_canonical_id = function(self, mv_id) -- -> number
      local mvinfo = getmvinfo(mv_id, self.mvs)
      if mvinfo.bound_mv_id then
        local final_id = self:get_canonical_id(mvinfo.bound_mv_id)
        if final_id ~= mvinfo.bound_mv_id then
          -- ok to mutate rather than setting in self.mvs here as collapsing chain is idempotent
          mvinfo.bound_mv_id = final_id
        end
        return final_id
      end
      return mv_id
    end,
  }
}

local function typechecker_state()
  return setmetatable({
      next_metavariable_id = 0,
      mvs = { prev_mvs = nil },
    }, typechecker_state_mt)
end

-- freeze and then commit or revert
-- like a transaction
local function speculate(f, ...)
  mvs = {
    prev_mvs = mvs,
  }
  local commit, result = f(...)
  if commit then
    -- commit
    for k, v in pairs(mvs) do
      if k ~= "prev_mvs" then
        prev_mvs[k] = mvs[k]
      end
    end
    mvs = mvs.prev_mvs
    return result
  else
    -- revert
    mvs = mvs.prev_mvs
    -- intentionally don't return result if set if not committing to prevent smuggling out of execution
    return nil
  end
end

-- checkable terms need a target type to typecheck against
local checkable = {
  inferred = function(inferred_term)
    return {
      kind = "inferred",
      inferred_term = inferred_term,
    }
  end,
  lambda = function(body) -- body is a checkable term
    return {
      kind = "checkable_lambda",
      body = body,
    }
  end,
}
-- inferrable terms can have their type inferred / don't need a target type
local inferrable = {
  level_type = {
    kind = "inferrable_level_type",
  },
  level0 = {
    kind = "inferrable_level0",
  },
  level_suc = function(previous_level) -- inferrable term
    return {
      kind = "inferrable_level_suc",
      previous_level = previous_level,
    }
  end,
  level_max = function(level_a, level_b) -- inferrable terms
    return {
      kind = "inferrable_level_max",
      level_a = level_a,
      level_b = level_b,
    }
  end,
  star = {
    kind = "inferrable_star",
  },
  prop = {
    kind = "inferrable_prop"
  },
  prim = {
    kind = "inferrable_prim"
  },
  annotated = function(annotated_term, annotated_type)
    return {
      kind = "inferrable_annotated",
      annotated_term = annotated_term,
      annotated_type = annotated_type,
    }
  end
}
-- typed terms have been typechecked but do not store their type internally
local typed = {
  lambda = function(body)
    return {
      kind = "typed_lambda",
      body = body,
    }
  end,
  level_type = {
    kind = "inferrable_level_type",
  },
  level0 = {
    kind = "typed_level0",
  },
  level_suc = function(previous_level) -- typed term
    return {
      kind = "typed_level_suc",
      previous_level = previous_level,
    }
  end,
  level_max = function(level_a, level_b) -- inferrable terms
    return {
      kind = "typed_level_max",
      level_a = level_a,
      level_b = level_b,
    }
  end,
  star = function(level) -- level number not a term
    return {
      kind = "typed_star",
      level = level,
    }
  end,
  prop = function(level) -- level number not a term
    return {
      kind = "typed_prop",
      level = level,
    }
  end,
  prim = {
    kind = "typed_prim",
  },
}
local values = {
  pi = function(
      argtype,
      arginfo,
      restype,
      resinfo)
    return {
      kind = "pi",
      argtype = argtype,
      arginfo = arginfo,
      restype = restype,
      resinfo = resinfo,
    }
  end,
  -- closure is a type that contains a typed term corresponding to the body
  -- and a runtime context representng the bound context where the closure was created
  closure = function()
      -- TODO
  end,
  level_type = {
    kind = "value_level_type",
  },
  level = function(level) -- the level number
      return {
        kind = "value_level",
        level = level,
      }
  end,
  star = function(level) -- the level number
      return {
        kind = "value_star",
        level = level,
      }
  end,
  prop = function(level) -- the level number
      return {
        kind = "value_prop",
        level = level,
      }
  end,
  prim = {
      kind = "value_prim",
  },
}

local function unify(
    first_value,
    second_value)
  -- -> unified value,
  if first_value == second_value then
    return first_value
  end

  -- eh this doesn't seem elegant/i have designed this wrong :ded:
  if getmetatable(first_value) == metavariable_mt then
    first_value:bind(second_value)
    return second_value
  elseif getmetatable(second_value) == metavariable_mt then
    second_value:bind(first_value)
    return first_value
  end

  error("unknown kind to unify")
end

local function check(
    checkable_term, -- constructed from checkable
    typechecking_context, -- todo
    target_type) -- must be unify with target type (there is some way we can assign metavariables to make them equal)
  -- -> type of that term, a typed term

  if checkable_term.kind == "inferred" then
    local inferred_type, typed_term = infer(checkable_term.inferred_term, typechecking_context)
    unified_type = unify(inferred_type, target_type) -- can fail, will cause lua error
    return unified_type, typed_term
  elseif checkable_term.kind == "checked_lambda" then
    -- assert that target_type is a pi type
    -- TODO open says work on other things first they will be easier
  end

  error("unknown kind in check: " .. checkable_term.kind)
end

local function infer(
    inferrable_term, -- constructed from inferrable
    typechecking_context -- todo
    )
  -- -> type of term, a typed term,
  if inferrable_term.kind == "inferrable_level0" then
    return values.level_type, typed.level0
  elseif inferrable_term.kind == "inferrable_level_suc" then
    local arg_type, arg_term = infer(inferrable_term.previous_level, typechecking_context)
    unify(arg_type, values.level_type)
    return values.level_type, typed.level_suc(arg_term)
  elseif inferrable_term.kind == "inferrable_level_max" then
    local arg_type_a, arg_term_a = infer(inferrable_term.level_a, typechecking_context)
    local arg_type_b, arg_term_b = infer(inferrable_term.level_b, typechecking_context)
    unify(arg_type_a, values.level_type)
    unify(arg_type_b, values.level_type)
    return values.level_type, typed.level_max(arg_term_a, arg_term_b)
  elseif inferrable_term.kind == "inferrable_level_type" then
    return values.star(0), typed.level_type
  elseif inferrable_term.kind == "inferrable_star" then
    return values.star(1), typed.star(0)
  elseif inferrable_term.kind == "inferrable_prop" then
    return values.star(1), typed.prop(0)
  elseif inferrable_term.kind == "inferrable_prim" then
    return values.star(1), typed.prim
  end

  error("unknown kind in infer: " .. inferrable_term.kind)
end

local function evaluate(
    typed_term,
    runtime_context
    )
  -- -> a value

  if typed_term.kind == "typed_level0" then
    return values.level(0)
  elseif typed_term.kind == "typed_level_suc" then
    local previous_level = evaluate(typed_term.previous_level, runtime_context)
    if previous_level.kind ~= "value_level" then
      p(previous_level)
      error("wrong type for previous_level")
    end
    if previous_level.level > 10 then
      error("NYI: level too high for typed_level_suc" .. tostring(previous_level.level))
    end
    return values.level(previous_level.level + 1)
  elseif typed_term.kind == "typed_level_max" then
    local level_a = evaluate(typed_term.level_a, runtime_context)
    local level_b = evaluate(typed_term.level_b, runtime_context)
    if level_a.kind ~= "value_level" or level_b.kind ~= "value_level" then
      error("wrong type for level_a or level_b")
    end
    return values.level(math.max(level_a.level, level_b.level))
  elseif typed_term.kind == "typed_level_type" then
    return values.level_type
  elseif typed_term.kind == "typed_star" then
    return values.star(typed_term.level)
  elseif typed_term.kind == "typed_prop" then
    return values.prop(typed_term.level)
  elseif typed_term.kind == "typed_prim" then
    return values.prim
  end

  error("unknown kind in evaluate " .. typed_term.kind)
end

return {
  checkable = checkable, -- {}
  inferrable = inferrable, -- {}
  check = check, -- fn
  infer = infer, -- fn
  typed = typed, -- {}
  evaluate = evaluate, -- fn
  values = values, -- {}
  unify = unify, -- fn
  typechecker_state = typechecker_state, -- fn (constructor)
}
