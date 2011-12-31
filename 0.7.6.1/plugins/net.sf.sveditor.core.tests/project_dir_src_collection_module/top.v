
`include "defines.svh"

`celldefine
module top();
	`include "class1.svh"
`protect	
	`make_function(def_function)
`endprotect	
endmodule


`celldefine
module top_t;

	sub subsys();
	
endmodule
`endcelldefine

