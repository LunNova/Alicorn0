-- TODO: this should not be here
-- used in check_arg_against_param
local function extract_value_metavariable(value) -- -> Option<metavariable>
  if value.kind == "value_free" and value.free_value.kind == "free_metavariable" then
    return value.free_value.metavariable
  end
  return nil
end

local function discard_self(fn)
  return function(self, ...)
    return fn(...)
  end
end

local function check_arg_against_param(param, arg)
  if param.value_check then
    if not param.value_check(arg) then
      p("p", arg)
      error("wrong argument type passed to constructor")
    end
  else
    local arg_mt = getmetatable(arg)
    if arg_mt ~= param and extract_value_metavariable(arg) == nil then
      p("mt", arg)
      error("wrong argument type passed to constructor")
    end
  end
end

local function gen_record(self, kind, params_with_types)
  local params = params_with_types.params
  local params_types = params_with_types.params_types
  -- ensure there are at least as many param types as there are params
  for i, _ in ipairs(params) do
    local v = params_types[i]
    if not v then
      error("nil passed to parameter type " .. tostring(i) .. " of " .. kind .. " (probable typo?)")
    end
  end
  local function record_cons(...)
    local args = { ... }
    local val = {
      kind = kind,
      params = params,
    }
    for i, v in ipairs(params) do
      local argi = args[i]
      check_arg_against_param(params_types[i], argi)
      val[v] = argi
    end
    setmetatable(val, self)
    return val
  end
  return record_cons
end

local function declare_record(self, kind, params_with_types)
  local record_cons = gen_record(self, kind, params_with_types)
  setmetatable(self, {
    __call = discard_self(record_cons),
  })
  return self
end

local function gen_unit(self, kind)
  local val = {
    kind = kind,
    params = {},
  }
  setmetatable(val, self)
  return val
end

local function declare_enum(self, name, variants)
  for _, v in ipairs(variants) do
    local vname = v[1]
    local kind = name .. "_" .. vname
    if v.params then
      self[vname] = gen_record(self, kind, v)
    else
      self[vname] = gen_unit(self, kind)
    end
  end
  setmetatable(self, nil)
  return self
end

local function declare_foreign(self, value_check)
  self.value_check = value_check
  setmetatable(self, nil)
  return self
end

local type_mt = {
  __index = {
    declare_record = declare_record,
    declare_enum = declare_enum,
    declare_foreign = declare_foreign,
  }
}

local function declare_type(self)
  setmetatable(self, type_mt)
  return self
end

return {
  declare_record = declare_record,
  declare_enum = declare_enum,
  declare_foreign = declare_foreign,
  declare_type = declare_type,
  gen_record = gen_record,
}
