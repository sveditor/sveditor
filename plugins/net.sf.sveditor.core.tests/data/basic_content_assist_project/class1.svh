
`ifndef INCLUDED_CLASS1_SVH    
`define INCLUDED_CLASS1_SVH

class class1;

	/****************************************************************
	 * new()
	 ****************************************************************/
	function new(int a, 
		int b);
	
		foo = boolean'(get_bit());
	endfunction
	
	
	function int get_data();
		return 'h5;
	endfunction
	
endclass

`endif /* INCLUDED_CLASS1_SVH */
