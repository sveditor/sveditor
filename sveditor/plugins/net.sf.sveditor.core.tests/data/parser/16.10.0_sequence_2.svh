
module m;
	
	sequence count_a_cycles;
		int x;
		($rose(a), x = 1)
		##1 (a, x++)[*0:$]
		##1 !a && (x <= MAX);
	endsequence	
	
endmodule

