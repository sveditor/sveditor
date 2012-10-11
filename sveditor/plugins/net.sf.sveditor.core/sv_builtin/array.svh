

class __sv_builtin_array #(type T=int);

	/**
	 * Function: size()
	 * The size() method returns the number of entries in the array. 
	 * If the array is empty, it returns 0.
	 */
	extern function int size();
	
endclass

class __sv_builtin_assoc_array #(type T=int, type IDX=int);

	/**
	 * Function: num()
	 * The num() and size() methods return the number of entries in the associative array. 
	 * If the array is empty, they return 0.
	 */
	extern function int num();
	
	extern function void delete(IDX index);
	
	extern function int exists(IDX index);
	
	extern function int first(ref IDX index);

	extern function int last(ref IDX index);

	extern function int next(ref IDX index);

	extern function int prev(ref IDX index);
	 
endclass
