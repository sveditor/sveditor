
`ifndef INCLUDED_CLASS1_SVH
`define INCLUDED_CLASS1_SVH
`include "missing_file.svh"

class class1;

	function new();
	
	endfunction
	
	
	function int get_data();
		if (foobar) begin
			if (foo2) begin
				foo = 2;
			end // end1
			foo2 = 5;
		end // end2
		return 5;
	endfunction
	
endclass

`endif /* INCLUDED_CLASS1_SVH */
