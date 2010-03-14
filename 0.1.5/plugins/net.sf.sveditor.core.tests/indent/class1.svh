
class class1 #(type T=int);

	function new();
		if (foo)
			foo = 5;
		else if (foo2) begin
			foo = 6;
		end

		do 
			foo++;
		while (foo < 5);

		do begin
			foo+=2;
		end while (foo < 20);

		forever
			foo += 5;

		forever begin
			foo += 5;
		end

		repeat (5) begin
			foo += 5;
		end

		while (foobar) begin
			foo = 2;

			if (foobar)
				foo = 2;
			else if (bar) begin
				foo = 5;
			end else
				bar = 6;

		end
	endfunction

	/**
	 * coverpoint foo
	 */
	covergroup foo;
		cp : coverpoint (foo) iff (foobar == 2);

		cp2 : coverpoint (foo) iff (foobar == 2) {
			bins foo[] = {1, 2, 3, 4};
			bins foo2[] = {3, 4, 5, 6};
		}

		cp3 : coverpoint (start[3:0]) {
			type_option.comment = "";
			option.at_least = 10;
			bins start1 = {0};
			bins start2 = {1};
		}

		startWidth_cp : coverpoint (startWidth[3:0]) {
			type_option.comment = "startWidth3_0";
			option.at_least = 10;
			bins width0 = {0};
			bins width1 = {1};
			bins width2 = {2};
			bins width3 = {3};
			bins width4 = {4};
			bins width5 = {5};
			bins width6 = {6};
			bins width7 = {7};
			bins width8 = {8};
			bins width9 = {9};
			bins width10 = {10};
			bins width11 = {11};
			bins width12 = {12};
			bins width13 = {13};
			bins width14 = {14};
			bins width15 = {15};
		}

		cp_cross : cross cp, cp2 iff (foo2);

		cp_cross : cross cp, cp2 iff (foo2) {
			bins ignore = intersect ();
		}
	endgroup

	constraint minPx_c {                                              
		if ((startWidth%(`maxPsums - af1_window_x)) == 0) { //even divide
			minPx == (startWidth/(`maxPsums - af1_window_x));
		} else {
			minPx == (startWidth/(`maxPsums - af1_window_x)) + 1;
		}
	}

endclass

package foobar;

	class foo;

		function new();
		endfunction

	endclass

endpackage

module top();

	class cls1;
		function new();
		endfunction
	endclass
endmodule
