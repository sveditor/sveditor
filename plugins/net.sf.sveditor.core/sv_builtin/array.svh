

class __sv_builtin_array #(type T=int);

	extern function int size();
	
endclass

class __sv_builtin_assoc_array #(type IDX=int, type T=int);

	extern function int num();
	
	extern function void delete(IDX index);
	
	extern function int exists(IDX index);
	
	extern function int first(ref IDX index);

	extern function int last(ref IDX index);

	extern function int next(ref IDX index);

	extern function int prev(ref IDX index);
	 
endclass
