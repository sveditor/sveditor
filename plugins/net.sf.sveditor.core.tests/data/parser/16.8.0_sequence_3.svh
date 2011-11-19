
module m;
	sequence s;
	a ##1 b ##1 c;
	endsequence
	sequence rule;
	@(posedge sysclk)
	trans ##1 start_trans ##1 s ##1 end_trans;
	endsequence
	
endmodule