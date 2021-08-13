

class c;

	task foo;
		unique0 if ((a==0) || (a==1)) $display("0 or 1");
		else if (a == 2) $display("2");
		else if (a == 4) $display("4"); // values 3,5,6,7
		// cause no violation report	
	endtask

endclass
