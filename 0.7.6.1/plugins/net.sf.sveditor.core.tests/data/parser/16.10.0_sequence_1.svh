
module m;
	sequence rep_v;
		int x = 0;
		(a[->1], x += data)[*4] ##1 b ##1 c && (data_out == x);
	endsequence	
endmodule
