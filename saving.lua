local terms = require "terms"
local gen = require "terms-generators"
local derivers = require "derivers"

-- the state is a combination of what needs to actually be saved
-- and lookup tables
-- after finsih loading stuff in to serialization state
-- create object storing just stuff to store
-- can toss the whole thing to json

-- api is calling serialize(term),
-- starts by creating a new serialization state,
-- serializes into the state
-- returns state
-- deserialize(state) returns a term that's __eq to the original

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

---@alias SerializedID integer

---@type {[Type] : fun(SerializationState, any) : SerializedID}
local serializers = {}
---@type {[Type] : fun(SerializationState, SerializedID) : unknown}
local deserializers = {}

-- Serializers for Lua built-in types

serializers["number"] = function(state, subject)
	return subject -- Numbers can be serialized as-is
end

serializers["string"] = function(state, subject)
	return subject -- Strings can be serialized as-is
end

serializers["boolean"] = function(state, subject)
	return subject -- Booleans can be serialized as-is
end

serializers["nil"] = function(state, subject)
	return subject -- nil can be serialized as-is
end

-- Deserializers for Lua built-in types

deserializers["number"] = function(state, id)
	return id -- Numbers can be deserialized as-is
end

deserializers["string"] = function(state, id)
	return id -- Strings can be deserialized as-is
end

deserializers["boolean"] = function(state, id)
	return id -- Booleans can be deserialized as-is
end

deserializers["nil"] = function(state, id)
	return id -- nil can be deserialized as-is
end

-- Handle tables (non-metatabled)
serializers["table"] = function(state, subject)
	local serialized = {}
	for k, v in pairs(subject) do
		if k == nil then
			error("Cannot serialize table with nil key")
		end
		if v == nil then
			error("Cannot serialize table with nil value")
		end
		serialized[serialize(state, k)] = serialize(state, v)
	end
	return serialized
end

deserializers["table"] = function(state, id)
	local deserialized = {}
	for k, v in pairs(id) do
		deserialized[deserialize(state, k)] = deserialize(state, v)
	end
	return deserialized
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
	end
	if not serializers[stype] then
		error("No serializer implemented for type: " .. tostring(stype))
	end
	return serializers[stype](state, subject)
end

---deserialize a value of unknown type
---@param state SerializationState
---@param id SerializedID
---@return any
local function deserialize(state, id)
	local stype = type(id)
	if stype == "table" then
		if not id.kind then
			error("Invalid serialization ID: missing 'kind' field")
		end
		stype = id.kind
	end
	if not deserializers[stype] then
		error("No deserializer implemented for type: " .. tostring(stype))
	end
	return deserializers[stype](state, id)
end

---serialize a value of a known type
---@param state SerializationState
---@param stype Type
---@param subject any
---@return SerializedID
local function serialize_known(state, stype, subject)
	if subject == nil then
		error("Cannot serialize nil value")
	end
	if not serializers[stype] then
		error("Known type has no serializer implemented: " .. tostring(stype))
	end
	return serializers[stype](state, subject)
end

---deserialize a value of a known type
---@param state SerializationState
---@param stype Type
---@param id SerializedID
---@return any
local function deserialize_known(state, stype, id)
	if not deserializers[stype] then
		error("Known type has no deserializer implemented: " .. tostring(stype))
	end
	return deserializers[stype](state, id)
end

---@type Deriver
local serialize_deriver = {
	record = function(t, info)
		if t.derived_serialize then
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

		deserializers[t] = function(state, id)
			local serialized = state.construction[id]
			local deserialized = {}
			for i, param in ipairs(params) do
				deserialized[param] = deserialize(state, serialized.args[i])
			end
			return setmetatable(deserialized, t)
		end

		idx.serialize = function(self)
			local state = { construction = {}, lookup = {} }
			return serialize(state, self), state
		end

		t.derived_serialize = true
	end,
	enum = function(t, info)
		if t.derived_serialize then
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

		deserializers[t] = function(state, id)
			local serialized = state.construction[id]
			local vname = serialized.kind:sub(#name + 2)
			local vdata = variants[vname]
			if not vdata then
				error("Unknown variant '" .. vname .. "' for enum '" .. name .. "'")
			end
			local deserialized = { kind = serialized.kind }

			if vdata.type == derivers.EnumDeriveInfoVariantKind.Record then
				for i, param in ipairs(vdata.info.params) do
					deserialized[param] = deserialize(state, serialized.args[i])
				end
			end

			return setmetatable(deserialized, t)
		end

		idx.serialize = function(self)
			local state = { construction = {}, lookup = {} }
			return serialize(state, self), state
		end

		t.derived_serialize = true
	end,
	foreign = function()
		error("can't derive :serialize() for a foreign type")
	end,
	map = function(t, info)
		if t.derived_serialize then
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

		idx.serialize = function(self)
			local state = { construction = {}, lookup = {} }
			return serialize(state, self), state
		end

		t.derived_serialize = true
	end,
	set = function(t, info)
		if t.derived_serialize then
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

		idx.serialize = function(self)
			local state = { construction = {}, lookup = {} }
			return serialize(state, self), state
		end

		t.derived_serialize = true
	end,
	array = function(t, info)
		if t.derived_serialize then
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

		methods.serialize = function(self)
			local state = { construction = {}, lookup = {} }
			return serialize(state, self), state
		end

		t.derived_serialize = true
	end,
}

-- Export the necessary functions and tables
return {
	serialize = serialize,
	deserialize = deserialize,
	serialize_known = serialize_known,
	deserialize_known = deserialize_known,
	serializers = serializers,
	deserializers = deserializers,
	serialize_deriver = serialize_deriver,
}
