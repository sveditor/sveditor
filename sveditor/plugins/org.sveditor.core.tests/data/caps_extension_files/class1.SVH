
`ifndef INCLUDED_CLASS1_SVH
`define INCLUDED_CLASS1_SVH

`ifdef ENABLE_CLASS1
class class1;

	function new();
	
	endfunction
	
	
	function int get_data();
		return 5;
	endfunction
	
	covergroup foobar;

		foo_cp : coverpoint (foo);

		foo2_cp : coverpoint foo2;

		foo_cross : cross foo_cp, foo2_cp {
			ignore_bins foo = (intersect etc);
		}
	endgroup
	
endclass
`endif /* ENABLE_CLASS1 */

`endif /* INCLUDED_CLASS1_SVH */
