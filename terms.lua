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

local function getmvinfo(id, mvs)
  if mvs == nil then
    return
  end
  -- if this is slow fixme later
  return mvs[id] or getmvinfo(id, mvs.prev_mvs)
end

local function unify(self, other)
  local self_mt = getmetatable(self)
  return self_mt.__unify(self, other)
end

local metavariable_mt

metavariable_mt = {
  __index = {
    get_value = function(self)
      local canonical = self:get_canonical()
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
    -- this gets called to bind to any value that isn't another metavariable
    bind_value = function(self, value)
      -- FIXME: if value is a metavariable (free w/ metavariable) call bind_metavariable here?
      local canonical = self:get_canonical()
      local canonical_info = getmvinfo(canonical.id, self.typechecker_state.mvs)
      if canonical_info.bound_value and canonical_info.bound_value ~= value then
        -- unify the two values, throws lua error if can't
        value = unify(canonical_info.bound_value, value)
      end
      self.typechecker_state.mvs[canonical.id] = {
        bound_value = value,
      }
      return value
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

local free = {
  metavariable = function(metavariable)
    if getmetatable(metavariable) ~= metavariable_mt then
      p("free.metavariable arg", metavariable)
      error("not a metavariable")
    end
    return {
      kind = "free_metavariable",
      metavariable = metavariable,
    }
  end,
  -- TODO: quoting and axiom
}

--[[
local quantity = {
  -- none
  erased = {
    kind = "quantity_erased"
  },
  -- one
  linear = {
    kind = "quantity_linear"
  },
  -- many
  unrestricted = {
    kind = "quantity_unrestricted"
  },
}

local visbility = {
  explicit = {
    kind = "visibility_explicit",
  },
  implicit = {
    kind = "visibility_implicit",
  },
}

local purity = {
  effectful = {
    kind = "purity_effectful",
  },
  pure = {
    kind = "purity_pure",
  }
}

-- WIP
local terms = generate_records {
  quantity = enum_variants { "erased", "linear", "unrestricted", },
  visibility = enum_variants { "explicit", "implicit", },
  purity = enum_variants { "effectful", "pure", },

  values = unifiable {
    arg_info = { TODO },
    pi = { TODO },
  },
}
--]]

local unifiable_simple_variant_mt = {
  __unify = function(self, other)
    if not other then
      error("can't unify " .. self.kind .. " with nil")
    elseif self ~= other then
      error("can't unify " .. self.kind .. " with " .. other.kind)
    end
    return self
  end,
}

local function unifiable_enum(data)
  local name = data[1]
  local res = {}
  for i, v in ipairs(data.variants) do
    res[v] = { kind = name .. '_' .. v }
    setmetatable(res[v], unifiable_simple_variant_mt)
  end
  return res
end

local quantity = unifiable_enum {"quantity", variants = {"erased", "linear", "unrestricted"} }
local visibility = unifiable_enum { "visibility", variants = { "explicit", "implicit" } }
local purity = unifiable_enum {"purity", variants = {"effectful", "pure"}}

-- local function record(variants, path)
--   if variants[0] then
--     return setmetatable(variant_table(variants, path), unifiable_simple_variant_mt)
--   end

-- end

-- local values = record({
--     pi = {
--       arg_type = value(),
--       arg_info = "arg_info",
--     },
--     arg_info = {
--       quantity = {
--         "erased",
--         "linear",
--         "unrestricted",
--       },
--       visibility = {
--         "explicit",
--         "implicit",
--       },
--     },
--     result_info = {
--       purity = {
--         "pure",
--         "effectful",
--       },
--     },
--     free = {
--       metavariable = {},
--       -- TODO quoting
--       -- TODO axiom
--     },
-- }, "value")

local function extract_value_metavariable(value) -- -> Option<metavariable>
  if value.kind == "value_free" and value.free_value.kind == "free_metavariable" then
    return value.free_value.metavariable
  end
  return nil
end

local function gen_unify_fn(params)
  return function(self, other) --> unified value
    if self == other then
      return self
    end

    local self_mv = extract_value_metavariable(self)
    local other_mv = extract_value_metavariable(other)

    if self_mv and other_mv then
      self_mv:bind_metavariable(other_mv)
      return self_mv:get_canonical()
    elseif self_mv then
      return self_mv:bind_value(other)
    elseif other_mv then
      return other_mv:bind_value(self)
    end

    if self.kind ~= other.kind then
      p(self.kind, other.kind)
      error("can't unify values of different kinds where neither is a metavariable")
    end

    local unified = {}
    local prefer_left = true
    local prefer_right = true
    for _, v in ipairs(params) do
      local sv = self[v]
      local ov = other[v]
      if sv.kind then
        local u = unify(sv, ov)
        unified[v] = u
        prefer_left = prefer_left and u == sv
        prefer_right = prefer_right and u == ov
      elseif sv ~= ov then
        p("unify args", self, other)
        error("unification failure as " .. v .. " field value doesn't match")
      end
    end

    if prefer_left then
      return self
    elseif prefer_right then
      return other
    else
      unified.kind = self.kind
      return unified
    end
  end
end

local values_mts = {
  quantity = {},
  visibility = {},
  arginfo = {},
  resultinfo = {},
  pi = {},
  closure = {},
  level_type = {},
  level = {},
  star = {},
  prop = {},
  prim = {},
  free = {},
}

local function gen_simple_value(name)
  values_mts[name].__unify = gen_unify_fn{}
  local val = {
    kind = "value_" .. name,
  }
  setmetatable(val, values_mts[name])
  return val
end

local function gen_param_value(name, params)
  values_mts[name].__unify = gen_unify_fn(params)
  return function(...)
    local args = { ... }
    local val = {
      kind = "value_" .. name,
    }
    for i, v in ipairs(params) do
      val[v] = args[i]
    end
    setmetatable(val, values_mts[name])
    return val
  end
end

local function gen_values(data)
  local values = {}
  for k, v in pairs(data) do
    local kt = type(k)
    local vt = type(v)
    if kt == "number" and vt == "string" then
      values[v] = gen_simple_value(v)
    elseif kt == "string" and vt == "table" then
      values[k] = gen_param_value(k, v)
    else
      error("gen_values: expected a string or a named sequence of strings, got " .. t)
    end
  end
  return values
end

local values = gen_values {
  -- erased, linear, unrestricted / none, one, many
  quantity = {"quantity"},
  -- explicit, implicit,
  visibility = {"visibility"},
  -- info about the argument (is it implicit / what are the usage restrictions?)
  arginfo = {"quantity", "visibility"},
  -- whether or not a function is effectful /
  -- for a function returning a monad do i have to be called in an effectful context or am i pure
  resultinfo = {"purity"},
  pi = {"argtype", "arginfo", "resulttype", "resultinfo"},
  -- closure is a type that contains a typed term corresponding to the body
  -- and a runtime context representng the bound context where the closure was created
  closure = {}, -- TODO
  "level_type",
  level = {"level"},
  star = {"level"},
  prop = {"level"},
  "prim",
}

local function discard_self(fn)
  return function(self, ...)
    return fn(...)
  end
end

-- fn(free_value) and table of functions eg free.metavariable(metavariable)
values.free = setmetatable({}, {
    __call = discard_self(gen_param_value("free", {"free_value"})) -- value should be constructed w/ free.something()
})
values.free.metavariable = function(mv)
  return values.free(free.metavariable(mv))
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
  quantity = quantity,
  visibility = visibility,
  purity = purity,
}
