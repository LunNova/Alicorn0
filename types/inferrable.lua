-- THIS FILE AUTOGENERATED BY terms-gen-meta.lua
---@meta "inferrable.lua"
---@class (exact) inferrable
inferrable = {}
---@return boolean
function inferrable:is_bound_variable() end
---@return number
function inferrable:unwrap_bound_variable() end
---@return boolean
function inferrable:is_typed() end
---@return value, any, typed
function inferrable:unwrap_typed() end
---@return boolean
function inferrable:is_annotated_lambda() end
---@return string, inferrable, inferrable, any
function inferrable:unwrap_annotated_lambda() end
---@return boolean
function inferrable:is_pi() end
---@return inferrable, checkable, inferrable, checkable
function inferrable:unwrap_pi() end
---@return boolean
function inferrable:is_application() end
---@return inferrable, checkable
function inferrable:unwrap_application() end
---@return boolean
function inferrable:is_tuple_cons() end
---@return any
function inferrable:unwrap_tuple_cons() end
---@return boolean
function inferrable:is_tuple_elim() end
---@return inferrable, inferrable
function inferrable:unwrap_tuple_elim() end
---@return boolean
function inferrable:is_tuple_type() end
---@return inferrable
function inferrable:unwrap_tuple_type() end
---@return boolean
function inferrable:is_record_cons() end
---@return any
function inferrable:unwrap_record_cons() end
---@return boolean
function inferrable:is_record_elim() end
---@return inferrable, any, inferrable
function inferrable:unwrap_record_elim() end
---@return boolean
function inferrable:is_enum_cons() end
---@return value, string, inferrable
function inferrable:unwrap_enum_cons() end
---@return boolean
function inferrable:is_enum_elim() end
---@return inferrable, inferrable
function inferrable:unwrap_enum_elim() end
---@return boolean
function inferrable:is_enum_type() end
---@return inferrable
function inferrable:unwrap_enum_type() end
---@return boolean
function inferrable:is_object_cons() end
---@return any
function inferrable:unwrap_object_cons() end
---@return boolean
function inferrable:is_object_elim() end
---@return inferrable, inferrable
function inferrable:unwrap_object_elim() end
---@return boolean
function inferrable:is_let() end
---@return string, inferrable, inferrable
function inferrable:unwrap_let() end
---@return boolean
function inferrable:is_operative_cons() end
---@return inferrable, inferrable
function inferrable:unwrap_operative_cons() end
---@return boolean
function inferrable:is_operative_type_cons() end
---@return checkable, inferrable
function inferrable:unwrap_operative_type_cons() end
---@return boolean
function inferrable:is_level_type() end
---@return boolean
function inferrable:is_level0() end
---@return boolean
function inferrable:is_level_suc() end
---@return inferrable
function inferrable:unwrap_level_suc() end
---@return boolean
function inferrable:is_level_max() end
---@return inferrable, inferrable
function inferrable:unwrap_level_max() end
---@return boolean
function inferrable:is_annotated() end
---@return checkable, inferrable
function inferrable:unwrap_annotated() end
---@return boolean
function inferrable:is_prim_tuple_cons() end
---@return any
function inferrable:unwrap_prim_tuple_cons() end
---@return boolean
function inferrable:is_prim_user_defined_type_cons() end
---@return any, any
function inferrable:unwrap_prim_user_defined_type_cons() end
---@return boolean
function inferrable:is_prim_tuple_type() end
---@return inferrable
function inferrable:unwrap_prim_tuple_type() end
---@return boolean
function inferrable:is_prim_function_type() end
---@return inferrable, inferrable
function inferrable:unwrap_prim_function_type() end
---@return boolean
function inferrable:is_prim_wrapped_type() end
---@return inferrable
function inferrable:unwrap_prim_wrapped_type() end
---@return boolean
function inferrable:is_prim_unstrict_wrapped_type() end
---@return inferrable
function inferrable:unwrap_prim_unstrict_wrapped_type() end
---@return boolean
function inferrable:is_prim_wrap() end
---@return inferrable
function inferrable:unwrap_prim_wrap() end
---@return boolean
function inferrable:is_prim_unstrict_wrap() end
---@return inferrable
function inferrable:unwrap_prim_unstrict_wrap() end
---@return boolean
function inferrable:is_prim_unwrap() end
---@return inferrable
function inferrable:unwrap_prim_unwrap() end
---@return boolean
function inferrable:is_prim_unstrict_unwrap() end
---@return inferrable
function inferrable:unwrap_prim_unstrict_unwrap() end
---@return boolean
function inferrable:is_prim_if() end
---@return checkable, inferrable, inferrable
function inferrable:unwrap_prim_if() end
---@return boolean
function inferrable:is_prim_intrinsic() end
---@return checkable, inferrable, any
function inferrable:unwrap_prim_intrinsic() end
---@class (exact) inferrableType:Type
---@field bound_variable fun(index:number): inferrable
---@field typed fun(type:value, usage_counts:any, typed_term:typed): inferrable
---@field annotated_lambda fun(param_name:string, param_annotation:inferrable, body:inferrable, anchor:any): inferrable
---@field pi fun(param_type:inferrable, param_info:checkable, result_type:inferrable, result_info:checkable): inferrable
---@field application fun(f:inferrable, arg:checkable): inferrable
---@field tuple_cons fun(elements:any): inferrable
---@field tuple_elim fun(subject:inferrable, body:inferrable): inferrable
---@field tuple_type fun(definition:inferrable): inferrable
---@field record_cons fun(fields:any): inferrable
---@field record_elim fun(subject:inferrable, field_names:any, body:inferrable): inferrable
---@field enum_cons fun(enum_type:value, constructor:string, arg:inferrable): inferrable
---@field enum_elim fun(subject:inferrable, mechanism:inferrable): inferrable
---@field enum_type fun(definition:inferrable): inferrable
---@field object_cons fun(methods:any): inferrable
---@field object_elim fun(subject:inferrable, mechanism:inferrable): inferrable
---@field let fun(name:string, expr:inferrable, body:inferrable): inferrable
---@field operative_cons fun(operative_type:inferrable, userdata:inferrable): inferrable
---@field operative_type_cons fun(handler:checkable, userdata_type:inferrable): inferrable
---@field level_type inferrable
---@field level0 inferrable
---@field level_suc fun(previous_level:inferrable): inferrable
---@field level_max fun(level_a:inferrable, level_b:inferrable): inferrable
---@field annotated fun(annotated_term:checkable, annotated_type:inferrable): inferrable
---@field prim_tuple_cons fun(elements:any): inferrable
---@field prim_user_defined_type_cons fun(id:any, family_args:any): inferrable
---@field prim_tuple_type fun(decls:inferrable): inferrable
---@field prim_function_type fun(param_type:inferrable, result_type:inferrable): inferrable
---@field prim_wrapped_type fun(type:inferrable): inferrable
---@field prim_unstrict_wrapped_type fun(type:inferrable): inferrable
---@field prim_wrap fun(content:inferrable): inferrable
---@field prim_unstrict_wrap fun(content:inferrable): inferrable
---@field prim_unwrap fun(container:inferrable): inferrable
---@field prim_unstrict_unwrap fun(container:inferrable): inferrable
---@field prim_if fun(subject:checkable, consequent:inferrable, alternate:inferrable): inferrable
---@field prim_intrinsic fun(source:checkable, type:inferrable, anchor:any): inferrable
return {}
