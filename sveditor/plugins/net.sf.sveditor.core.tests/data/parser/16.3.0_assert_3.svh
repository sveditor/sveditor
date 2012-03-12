

module m;
	
	initial begin
		assert (myfunc(a,b)) count1 = count + 1; else ->event1;
		assert (y == 0) else flag = 1;		
	end
	
endmodule