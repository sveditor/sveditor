
class c;
	struct packed signed {
		int a;
		shortint b;
		byte c;
		bit [7:0] d;
	} pack1; // signed, 2-state
	
	struct packed unsigned {
		time a;
		integer b;
		logic [31:0] c;
	} pack2; // unsigned, 4-state	
	
endclass
