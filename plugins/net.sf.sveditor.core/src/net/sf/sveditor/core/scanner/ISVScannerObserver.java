package net.sf.sveditor.core.scanner;

import java.util.List;

public interface ISVScannerObserver {
	
	int FieldAttr_Local             = (1 << 0);
	int FieldAttr_Protected			= (1 << 1);
	int FieldAttr_Rand				= (1 << 2);
	int FieldAttr_Randc				= (1 << 3);
	int FieldAttr_Static            = (1 << 4);
	int FieldAttr_Virtual			= (1 << 5);
	int FieldAttr_Automatic         = (1 << 6);
	int FieldAttr_Extern            = (1 << 7);
	int FieldAttr_Const             = (1 << 8);
	int FieldAttr_DPI				= (1 << 9);
	int FieldAttr_Pure				= (1 << 10);
	int FieldAttr_Context			= (1 << 11);
	
	int ParamAttr_Virtual           = (1 << 0);
	int ParamAttr_Ref               = (1 << 1);
	int ParamAttr_Input				= (1 << 2);
	int ParamAttr_Output			= (1 << 3);
	int ParamAttr_Inout				= (1 << 4);
	
	String ModIfcInstPref           = "@@module_ifc@@";
	
	void error(String msg);
	
	void init(ISVScanner scanner);
	
	void enter_file(String filename);
	
	void leave_file();
	
	void import_statment(String imp) throws HaltScanException;
	
	void enter_preproc_conditional(String type, String conditional);
	
	void leave_preproc_conditional();
	
	/**
	 * 
	 * @param name
	 * @param ports
	 * @throws HaltScanException
	 */
	void enter_module_decl(
			String 			name, 
			String			ports) throws HaltScanException;
	
	void enter_program_decl(
			String			name) throws HaltScanException;
	
	void enter_interface_decl(
			String			name,
			String			ports) throws HaltScanException;
	
	void leave_interface_decl();
	
	void enter_class_decl(
			String						name,
			List<SVClassIfcModParam>	params,
			String						super_name,
			List<SVClassIfcModParam>	super_params
			) throws HaltScanException;
			
	
	void enter_struct_decl(
			String						name,
			List<SVClassIfcModParam>	params) throws HaltScanException;
	
	void leave_struct_decl();
	/**
	 * Handles all 
	 * @param type
	 * @param variables
	 * @throws HaltScanException
	 */
	void variable_decl(SVTypeInfo type, int attr, List<String> variables) 
		throws HaltScanException;
	
	void leave_module_decl() throws HaltScanException;
	
	void leave_program_decl() throws HaltScanException;
	
	void leave_class_decl() throws HaltScanException;

	/**
	 * 
	 * @param name
	 * @param params
	 * @throws HaltScanException
	 */
	void enter_task_decl(
			String					name,
			int						attr,
			List<SVTaskFuncParam>	params) 
				throws HaltScanException;

	void enter_func_decl(
			String					name,
			int						attr,
			String					ret_type,
			List<SVTaskFuncParam>	params) 
				throws HaltScanException;

	void leave_task_decl();

	void leave_func_decl();
	
	void preproc_define(String key, List<String> params, String value);
	
	void preproc_include(String path);
	
	void comment(String comment);
	
	
	void enter_package(String name);
	
	void leave_package();
	
	void enter_covergroup(String name);

	void leave_covergroup();
	
	void covergroup_item(String name, String type);
	
	void constraint(String name, String expr);
	
	void enter_sequence(String name);
	
	void leave_sequence();
	
	void enter_property(String name);
	
	void leave_property();
}
