
`ifndef INCLUDED_CLASS1_SVH
`define INCLUDED_CLASS1_SVH

`ifdef ENABLE_CLASS1
class class1;

	function new();
	
	endfunction
	
	
	function int get_data();
		return 5;
	endfunction
	
endclass
`endif /* ENABLE_CLASS1 */

`endif /* INCLUDED_CLASS1_SVH */
