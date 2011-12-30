module m;
	sequence delay_arg_example (max, shortint delay1, delay2, min);
	x ##delay1 y[*min:max] ##delay2 z;
	endsequence
	
	parameter my_delay=2;
	
	cover property (delay_arg_example($, my_delay, my_delay-1, 3));

	cover property (x ##2 y[*3:$] ##1 z);
	
endmodule