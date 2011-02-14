/****************************************************************************
 * ${filename}
 ****************************************************************************/
#ifndef INCLUDED_${classname}_svh
#define INCLUDED_${classname}_svh

class ${classname} extends ${superclass};

	`ovm_component_utils(${classname})

	${function_new}
	
	/****************************************************************
	 * build()
	 ****************************************************************/
	virtual function void build();
		super.build();
	endfunction

	/****************************************************************
	 * connect()
	 ****************************************************************/
	virtual function void connect();
		super.connect();
	endfunction

	/****************************************************************
	 * run()
	 ****************************************************************/
	virtual task run();
		super.run();
	endfunction
	
endclass

#endif /* INCLUDED_${classname}_svh
