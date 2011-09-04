
`include "defines.svh"

`celldefine
module top();
	`include "class1.svh"
	
	`make_function(def_function)
	
endmodule


`celldefine
module top_t;

	sub subsys();
	
endmodule
`endcelldefine

