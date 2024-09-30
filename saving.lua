local terms = require "terms"
local gen = require "terms-generators"
local derivers = require "derivers"

-- the state is a combination of what needs to actually be saved
-- and lookup tables
-- after finishing loading stuff into serialization state
-- create object storing just stuff to store
-- can toss the whole thing to json

-- api is calling serialize(term),
-- starts by creating a new serialization state,
-- serializes into the state
-- returns state
-- deserialize(state) returns a term that's __eq to the original

-- FIXME: not fully following above plan atm

---@class SerializedEnum
---@field kind string
---@field args integer[]

---@class EnumSerializationState
---@field construction SerializedEnum[]
---@field lookup {[any] : integer}

---@class SerializationState
---@field host_intrinsics string[]
---@field host_intrinsics_lookup {[string] : integer}
---@field metavariable_lookup {[Metavariable] : integer}
---@field metavariable_count integer
---@field enums {[string] : EnumSerializationState}
---@field construction any[]
---@field lookup {[any] : integer}

---@alias SerializedID integer

---@type {[Type] : fun(SerializationState, any) : SerializedID}
local serializers = {}
---@type {[Type] : fun(SerializationState, SerializedID) : unknown}
local deserializers = {}

-- Serializers for Lua built-in types

-- FIXME: jank
serializers["__number"] = function(state, subject)
	-- FIXME: this is a hack to allow serializing numbers when serialization IDs are also numbers
	local serialized = { kind = "__number", value = subject }
	table.insert(state.construction, serialized)
	return #state.construction
end

-- FIXME: jank
deserializers["__number"] = function(state, id)
	return state.construction[id].value
end

-- these built-in types don't need a deserializer impl because they are stored as-is
serializers["__string"] = function(state, subject)
	return subject
end
serializers["__boolean"] = function(state, subject)
	return subject
end
serializers["__nil"] = function(state, subject)
	return subject
end

---serialize a value of unknown type
---@param state SerializationState
---@param subject any
---@return SerializedID
local function serialize(state, subject)
	if subject == nil then
		error("Cannot serialize nil value")
	end
	local stype = type(subject)
	if stype == "table" then
		stype = getmetatable(subject) or "table"
	else
		stype = "__" .. stype
	end
	if not serializers[stype] then
		error("No serializer implemented for type: " .. tostring(stype))
	end

	-- Check if the subject has already been serialized
	if state.lookup[subject] then
		return state.lookup[subject]
	end

	-- Serialize the subject and store the ID
	local id = serializers[stype](state, subject)
	state.lookup[subject] = id
	return id
end

---deserialize a value of unknown type
---@param state SerializationState
---@param id SerializedID
---@return any
local function deserialize(state, id)
	if type(id) ~= "number" then
		--error("Invalid serialization ID: expected number, got " .. type(id))
		return id
	end
	if id < 1 or id > #state.construction then
		error("Invalid serialization ID: out of range")
	end
	local serialized = state.construction[id]
	if type(serialized) ~= "table" or not serialized.kind then
		error("Invalid serialized object: missing 'kind' field")
	end
	-- p(serialized)
	local stype = serialized.kind
	if not deserializers[stype] then
		error("No deserializer implemented for type: " .. tostring(stype))
	end
	return deserializers[stype](state, id)
end

local already_derived = {}

---@type Deriver
local serialize_deriver = {
	record = function(t, info)
		if already_derived[t] then
			return
		end

		local idx = t.__index or {}
		t.__index = idx
		local kind = info.kind
		local params = info.params

		serializers[t] = function(state, self)
			local serialized = { kind = kind, args = {} }
			for _, param in ipairs(params) do
				if self[param] == nil then
					error("Missing parameter '" .. param .. "' in record of type '" .. kind .. "'")
				end
				table.insert(serialized.args, serialize(state, self[param]))
			end
			table.insert(state.construction, serialized)
			return #state.construction
		end

		deserializers[kind] = function(state, id)
			local serialized = state.construction[id]
			local deserialized = {}
			for i, param in ipairs(params) do
				deserialized[i] = deserialize(state, serialized.args[i])
			end
			return t(table.unpack(deserialized))
		end

		already_derived[t] = true
	end,
	enum = function(t, info)
		if already_derived[t] then
			return
		end

		local idx = t.__index or {}
		t.__index = idx
		local name = info.name
		local variants = info.variants

		serializers[t] = function(state, self)
			local vname = self.kind:sub(#name + 2)
			local vdata = variants[vname]
			if not vdata then
				error("Unknown variant '" .. vname .. "' for enum '" .. name .. "'")
			end
			local serialized = { kind = self.kind, args = {} }

			if vdata.type == derivers.EnumDeriveInfoVariantKind.Record then
				for _, param in ipairs(vdata.info.params) do
					if self[param] == nil then
						error(
							"Missing parameter '"
								.. param
								.. "' in enum variant '"
								.. vname
								.. "' of type '"
								.. name
								.. "'"
						)
					end
					table.insert(serialized.args, serialize(state, self[param]))
				end
			end

			table.insert(state.construction, serialized)
			return #state.construction
		end

		-- Generate variant-specific deserializers
		for vidx, vname in ipairs(variants) do
			local vdata = variants[vname]
			local full_name = name .. "." .. vname

			if vdata.type == derivers.EnumDeriveInfoVariantKind.Record then
				deserializers[full_name] = function(state, id)
					local serialized = state.construction[id]
					local deserialized = {}
					for i, param in ipairs(vdata.info.params) do
						-- print("Calling deserialize for arg ", serialized.args[i])
						deserialized[i] = deserialize(state, serialized.args[i])
						-- print("Got ", deserialized[i], type(deserialized[i]))
					end
					-- print("Calling constructor for " .. full_name)
					return t[vname](table.unpack(deserialized))
				end
			elseif vdata.type == derivers.EnumDeriveInfoVariantKind.Unit then
				deserializers[full_name] = function(state, id)
					return t[vname]
				end
			else
				error(
					"NYI Can't generate deserializer for variant "
						.. vname
						.. " of enum "
						.. name
						.. " with variant type "
						.. vdata.type
				)
			end
		end

		already_derived[t] = true
	end,
	foreign = function()
		error("can't derive :serialize() for a foreign type")
	end,
	--FIXME: idk if this is right or how to test
	map = function(t, info)
		if already_derived[t] then
			return
		end

		local idx = t.__index

		serializers[t] = function(state, self)
			local serialized = { kind = "map", args = {} }
			for k, v in pairs(self._map) do
				if k == nil then
					error("Cannot serialize map with nil key")
				end
				if v == nil then
					error("Cannot serialize map with nil value")
				end
				table.insert(serialized.args, serialize(state, k))
				table.insert(serialized.args, serialize(state, v))
			end
			table.insert(state.construction, serialized)
			return #state.construction
		end

		deserializers[t] = function(state, id)
			local serialized = state.construction[id]
			local deserialized = t()
			for i = 1, #serialized.args, 2 do
				local k = deserialize(state, serialized.args[i])
				local v = deserialize(state, serialized.args[i + 1])
				deserialized:set(k, v)
			end
			return deserialized
		end

		already_derived[t] = true
	end,
	--FIXME: idk if this is right or how to test
	set = function(t, info)
		if already_derived[t] then
			return
		end

		local idx = t.__index

		serializers[t] = function(state, self)
			local serialized = { kind = "set", args = {} }
			for k in pairs(self._set) do
				if k == nil then
					error("Cannot serialize set with nil value")
				end
				table.insert(serialized.args, serialize(state, k))
			end
			table.insert(state.construction, serialized)
			return #state.construction
		end

		deserializers[t] = function(state, id)
			local serialized = state.construction[id]
			local deserialized = t()
			for _, arg in ipairs(serialized.args) do
				deserialized:put(deserialize(state, arg))
			end
			return deserialized
		end

		already_derived[t] = true
	end,
	--FIXME: idk if this is right or how to test
	array = function(t, info)
		if already_derived[t] then
			return
		end

		local methods = t.methods

		serializers[t] = function(state, self)
			local serialized = { kind = "array", args = {} }
			for i = 1, self:len() do
				if self[i] == nil then
					error("Cannot serialize array with nil value at index " .. i)
				end
				table.insert(serialized.args, serialize(state, self[i]))
			end
			table.insert(state.construction, serialized)
			return #state.construction
		end

		deserializers[t] = function(state, id)
			local serialized = state.construction[id]
			local deserialized = t()
			for _, arg in ipairs(serialized.args) do
				deserialized:push(deserialize(state, arg))
			end
			return deserialized
		end

		already_derived[t] = true
	end,
}

-- Export the necessary functions and tables
return {
	serialize = function(term)
		local state = { construction = {}, lookup = {} }
		local id = serialize(state, term)
		--assert(id == 1)
		--FIXME: ???
		-- is this API right now?
		return state
	end,
	deserialize = function(state)
		return deserialize(state, #state.construction)
	end,
	serialize_deriver = serialize_deriver,
}
