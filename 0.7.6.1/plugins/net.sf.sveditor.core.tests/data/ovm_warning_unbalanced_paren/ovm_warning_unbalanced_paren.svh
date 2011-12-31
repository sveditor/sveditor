

`include "ovm_macros.svh

class ovm_warning_unbalanced_paren;

	function test;
		`ovm_warning("WARN", $sformatf("(%s", str))
	endfunction

endclass

