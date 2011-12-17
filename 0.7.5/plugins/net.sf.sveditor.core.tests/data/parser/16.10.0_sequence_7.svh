
module m;

	sequence sub_seq3(lv);
		int lv; // illegal because lv is a formal argument
		(a ##1 !a, lv = data_in) ##1 !b[*0:$] ##1 b && (data_out == lv);
	endsequence
	
endmodule
