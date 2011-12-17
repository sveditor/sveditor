
module m;
	sequence s1;
	@(posedge sysclk) (x ##1 s2);	
	endsequence
	sequence s2;
	@(posedge sysclk) (y ##1 s1);
	endsequence	
endmodule