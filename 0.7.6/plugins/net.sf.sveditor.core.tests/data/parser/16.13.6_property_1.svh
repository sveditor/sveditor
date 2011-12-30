
module m;
	property data_end;
		@(posedge mclk)
		data_phase |-> ((irdy==0) && ($fell(trdy) || $fell(stop))) ;
	endproperty	
	
endmodule