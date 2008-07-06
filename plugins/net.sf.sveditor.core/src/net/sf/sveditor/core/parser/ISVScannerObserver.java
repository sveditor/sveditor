package net.sf.sveditor.core.parser;

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
	
	int ParamAttr_Virtual           = (1 << 0);
	int ParamAttr_Ref               = (1 << 1);
	int ParamAttr_Input				= (1 << 2);
	int ParamAttr_Output			= (1 << 3);
	int ParamAttr_Inout				= (1 << 4);
	
	void error(String msg);
	
	void init(ISVScanner scanner);
	
	void enter_file(String filename);
	
	void leave_file();
	
	void import_statment(String imp) throws HaltScanException;
	
	/**
	 * 
	 * @param name
	 * @param ports
	 * @throws HaltScanException
	 */
	void enter_module_decl(
			String 			name, 
			String			ports) throws HaltScanException;
	
	void enter_interface_decl(
			String			name,
			String			ports) throws HaltScanException;
	
	void leave_interface_decl();
	
	void enter_class_decl(
			String						name,
			List<SVClassIfcModParam>	params) throws HaltScanException;
			
	
	/**
	 * Handles all 
	 * @param type
	 * @param variables
	 * @throws HaltScanException
	 */
	void variable_decl(String type, int attr, List<String> variables) 
		throws HaltScanException;
	
	void leave_module_decl() throws HaltScanException;
	
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
	
	void leave_task_decl();
	
	
	void preproc_define(String key, List<String> params, String value);
	
	void preproc_include(String path);
	
	
	void enter_package(String name);
	
	void leave_package();
			
}
