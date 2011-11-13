
module m;
	sequence s20_1(data,en);
	(!frame && (data==data_bus)) ##1 (c_be[0:3] == en);
	endsequence	
endmodule
