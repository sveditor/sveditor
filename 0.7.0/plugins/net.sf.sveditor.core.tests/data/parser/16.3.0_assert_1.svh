
class c;
	function void test;
		assert_f: assert(f) $info("passed"); else $error("failed");
		assume_inputs: assume (in_a || in_b) $info("assumption holds");
			else $error("assumption does not hold");
		cover_a_and_b: cover (in_a && in_b) $info("in_a && in_b == 1 covered");
	endfunction
endclass

