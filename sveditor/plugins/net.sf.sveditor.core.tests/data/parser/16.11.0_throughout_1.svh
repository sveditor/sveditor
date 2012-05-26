
module m;
	sequence burst_rule1;
		@(posedge mclk)
		$fell(burst_mode) ##0
		((!burst_mode) throughout (##2 ((trdy==0)&&(irdy==0)) [*7]));
	endsequence
endmodule