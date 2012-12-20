

class c;

	task foo;
		unique if ((a==0) || (a==1)) $display("0 or 1");
		else if (a == 2) $display("2");
		else if (a == 4) $display("4"); // values 3,5,6,7 cause a violation report
		priority if (a[2:1]==0) $display("0 or 1");
		else if (a[2] == 0) $display("2 or 3");
		else $display("4 to 7"); // covers all other possible values,
		// so no violation report
	endtask

endclass
