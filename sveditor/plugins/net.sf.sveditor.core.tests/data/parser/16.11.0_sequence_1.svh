
module m;
	
	sequence s1;
		logic v, w;
		(a, v = e) ##1
		(b[->1], w = f, $display("b after a with v = %h, w = %h\n", v, w));
	endsequence	
	
endmodule