
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

		cp_cross : cross cp, cp2 iff (foo2);

		cp_cross : cross cp, cp2 iff (foo2) {
			bins ignore = intersect ();
		}
	endgroup

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
