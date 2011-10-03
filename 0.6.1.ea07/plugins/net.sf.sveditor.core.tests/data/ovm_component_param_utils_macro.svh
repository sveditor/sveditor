
`include "ovm_macros.svh"

class ovm_component_param_utils_macro  #( type T = int ,
     type comp_type = ovm_built_in_comp #( T ) ,
     type convert = ovm_built_in_converter #( T ) ,
     type pair_type = ovm_built_in_pair #( T ) )
    extends ovm_component;

	typedef ovm_in_order_comparator #(T,comp_type,convert,pair_type) this_type;
	`ovm_component_param_utils(this_type)
	
endclass