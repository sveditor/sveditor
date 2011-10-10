
class c;
	typedef union { int i; shortreal f; } num; // named union type
	num n;
	
	typedef struct {
		bit isfloat;
		union { int i; shortreal f; } n; // anonymous union type
	} tagged_st; // named structure

	tagged_st ts;

	function void test;
		n.f = 0.0; // set n in floating point format
		ts.n.f = 0.0;
	endfunction
	
endclass