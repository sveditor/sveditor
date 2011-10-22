
module m;
	`define data_end_exp (data_phase && ((irdy==0)&&($fell(trdy)||$fell(stop))))
	property data_end_rule1;
		@(posedge mclk)
		`data_end_exp |-> ##[1:2] $rose(frame) ##1 $rose(irdy);
	endproperty	
endmodule