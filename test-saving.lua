local terms = require "terms"
local saving = require "saving"
local gen = require "terms-generators"
local array = gen.declare_array
local value_array = array(terms.value)

-- Create some sample terms
local sample_number = terms.value.number(42)
local sample_string = terms.value.host_value("Hello, world!")
local sample_tuple =
	terms.value.tuple_value(value_array(terms.value.number(1), terms.value.host_value("two"), terms.value.number(3)))

local sample_enum = terms.value.enum_value(
	"cons",
	terms.tup_val(terms.value.number(1), terms.value.enum_value("empty", terms.tup_val()))
)

terms.value:derive(saving.serialize_deriver)
terms.neutral_value:derive(saving.serialize_deriver)
terms.typed_term:derive(saving.serialize_deriver)
terms.inferrable_term:derive(saving.serialize_deriver)
terms.checkable_term:derive(saving.serialize_deriver)
terms.binding:derive(saving.serialize_deriver)
terms.expression_goal:derive(saving.serialize_deriver)
terms.free:derive(saving.serialize_deriver)
terms.visibility:derive(saving.serialize_deriver)
terms.purity:derive(saving.serialize_deriver)
terms.result_info:derive(saving.serialize_deriver)

-- Test the serialization for each term type
local function test_serialization(term_name, term)
	local inner_error_logged = false
	local ok, result = pcall(function()
		local state = saving.serialize(term)
		local loaded = saving.deserialize(state)
		if not terms.value.__eq(term, loaded) then
			p("Term:", term, "Type:", type(term))
			p("State:", state)
			p("Loaded:", loaded, "Type:", type(loaded))
			if type(term) == "table" and type(loaded) == "table" and term.default_print and loaded.default_print then
				print("Term (default_print):")
				print(term:default_print())
				print("Loaded (default_print):")
				print(loaded:default_print())
			end
			return false
		end
		return true
	end)
	if ok then
		print(term_name .. " saving/loading pass: " .. tostring(result))
	else
		print(term_name .. " saving/loading failed")
		print("Error: " .. tostring(result))
		print("Attempted to serialize:")
		p(term)
	end
end

test_serialization("Number", sample_number)
test_serialization("String", sample_string)
test_serialization("Tuple", sample_tuple)
test_serialization("Enum", sample_enum)

-- Additional tests using test_serialization function
local sample_level = terms.value.level(3)
test_serialization("Level", sample_level)

local sample_star = terms.value.star(2, 1)
test_serialization("Star", sample_star)

local sample_prop = terms.value.prop(1)
test_serialization("Prop", sample_prop)

local sample_pi = terms.value.pi(
	terms.value.number_type,
	terms.value.param_info(terms.value.visibility(terms.visibility.explicit)),
	terms.value.number_type,
	terms.value.result_info(terms.result_info(terms.purity.pure))
)
test_serialization("Pi", sample_pi)

local sample_closure = terms.value.closure("x", terms.typed_term.literal(terms.unit_val), terms.runtime_context())
test_serialization("Closure", sample_closure)
