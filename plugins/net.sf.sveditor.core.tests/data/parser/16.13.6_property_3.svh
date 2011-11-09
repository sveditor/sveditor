
module m;
	
	property data_end_rule2;
		@(posedge mclk) ##[1:2] $rose(frame) ##1 $rose(irdy);
	endproperty	

	
	property p_wready_x;
		@(posedge pb_clk)
		disable iff (disable_assertions_for_x)
		(pb_wdata_ready !== 1'bx);
	endproperty
	
	
endmodule