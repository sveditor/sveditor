
module m;
	
	property e;
		int x;
		(valid_in, x = pipe_in) |-> ##5 (pipe_out1 == (x+1));
	endproperty	
	
endmodule