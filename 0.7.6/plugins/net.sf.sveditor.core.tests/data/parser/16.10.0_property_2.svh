
module m;
	sequence data_check;
		int x;
		a ##1 (!a, x = data_in) ##1 !b[*0:$] ##1 b && (data_out == x);
	endsequence
	
	property data_check_p;
		int x;
		a ##1 (!a, x = data_in) |=> !b[*0:$] ##1 b && (data_out == x);
	endproperty
endmodule