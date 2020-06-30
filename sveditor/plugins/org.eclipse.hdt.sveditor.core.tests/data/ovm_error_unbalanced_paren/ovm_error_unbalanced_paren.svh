

`include "ovm_macros.svh"

class ovm_error_unbalanced_paren;

	function test;
		`ovm_error("a", ("this string has a paren in it )"))
	endfunction

endclass