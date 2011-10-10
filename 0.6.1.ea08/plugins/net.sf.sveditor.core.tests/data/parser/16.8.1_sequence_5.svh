
module m;
	sequence s(bit a, bit b);
	bit loc_a;
	(1'b1, loc_a = a) ##0
	(t == loc_a) [*0:$] ##1 b;
	endsequence	
	
endmodule