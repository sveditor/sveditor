
`ifndef INCLUDED_CLASS2_SVH
`define INCLUDED_CLASS2_SVH
`include "defines.svh"

class class2;

	function new();
	
	endfunction
	
	`make_function(def_function)
	
	`accessor_func
	
	function int get_data();
		return 5;
	endfunction
	
endclass

`endif /* INCLUDED_CLASS2_SVH */
