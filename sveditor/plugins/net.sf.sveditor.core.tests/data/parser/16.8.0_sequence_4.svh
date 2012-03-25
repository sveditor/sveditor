
module m;
	sequence rule;
	@(posedge sysclk)
	trans ##1 start_trans ##1 (a ##1 b ##1 c) ##1 end_trans ;
	endsequence	
endmodule