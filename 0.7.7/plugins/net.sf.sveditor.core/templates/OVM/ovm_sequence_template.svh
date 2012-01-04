/****************************************************************************
 * ${filename}
 ****************************************************************************/
#ifndef INCLUDED_${classname}_svh
#define INCLUDED_${classname}_svh

class ${classname} extends ${superclass};

	`ovm_object_utils(${classname})

	${function_new}
	
	/****************************************************************
	 * body()
	 ****************************************************************/
	virtual task body();
	endtask

endclass

#endif /* INCLUDED_${classname}_svh
