
module m;
	
	property data_end_rule2;
		@(posedge mclk) ##[1:2] $rose(frame) ##1 $rose(irdy);
	endproperty	
	
endmodule