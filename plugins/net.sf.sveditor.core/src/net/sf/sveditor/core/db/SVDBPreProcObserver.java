package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.scanner.HaltScanException;
import net.sf.sveditor.core.scanner.ISVScanner;
import net.sf.sveditor.core.scanner.ISVScannerObserver;
import net.sf.sveditor.core.scanner.SVClassIfcModParam;
import net.sf.sveditor.core.scanner.SVTaskFuncParam;
import net.sf.sveditor.core.scanner.SVTypeInfo;
import net.sf.sveditor.core.scanner.SvVarInfo;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVDBPreProcObserver implements ISVScannerObserver {
	private List<SVDBFile>              fFileList;
	private Stack<SVDBScopeItem>		fScopeStack;
	private ISVScanner					fScanner;
	
	
	public SVDBPreProcObserver() {
		fFileList = new ArrayList<SVDBFile>();
		fScopeStack = new Stack<SVDBScopeItem>();
	}
	
	public List<SVDBFile> getFiles() {
		return fFileList;
	}

	
	public void init(ISVScanner scanner) {
		fScanner = scanner;
	}

	
	public void enter_file(String filename) {
		SVDBFile file = new SVDBFile(filename);
		fFileList.add(file);
		
		fScopeStack.push(file);
	}
	
	
	public void enter_package(String name) {
		SVDBPackageDecl pd = new SVDBPackageDecl(name);
		setLocation(pd);
		fScopeStack.peek().addItem(pd);
		fScopeStack.push(pd);
	}
	
	
	public void leave_package() {
		if (fScopeStack.peek() instanceof SVDBPackageDecl) {
			fScopeStack.pop();
		}
	}
	
	
	public void preproc_define(String key, List<String> params, String value) {
		SVDBMacroDef def = new SVDBMacroDef(key, params, value);
		setLocation(def);
		fScopeStack.peek().addItem(def);
	}
	
	
	public void enter_preproc_conditional(String type, String conditional) {
		SVDBPreProcCond c = new SVDBPreProcCond(type, conditional);
		setLocation(c);
		
		fScopeStack.peek().addItem(c);
		fScopeStack.push(c);
	}

	public void leave_preproc_conditional() {
		fScopeStack.pop();
	}

	public void preproc_include(String path) {
		SVDBInclude inc = new SVDBInclude(path);
		setLocation(inc);
		fScopeStack.peek().getItems().add(inc);
	}
	
	
	public void leave_file() {
		fScopeStack.clear();
	}
	
	private void setLocation(SVDBItem it) {
		ScanLocation loc = fScanner.getStmtLocation();
		
		it.setLocation(new SVDBLocation(
				fFileList.get(fFileList.size()-1), 
				loc.getLineNo(), loc.getLinePos()));
	}
	
	
	public void error(String msg) {
		System.out.println("[ERROR] " + msg);
	}


	
	public void comment(String comment) {}

	
	public void covergroup_item(String name, String type, String target, String body) {}

	
	public void enter_class_decl(String name, List<SVClassIfcModParam> params,
			String super_name, List<SVClassIfcModParam> super_params)
			throws HaltScanException {}

	
	public void enter_covergroup(String name) {}

	
	public void enter_func_decl(String name, int attr, String ret_type,
			List<SVTaskFuncParam> params) throws HaltScanException {}

	
	public void enter_interface_decl(String name, String ports)
			throws HaltScanException {}

	
	public void enter_module_decl(String name, String ports)
			throws HaltScanException {}
	
	public void enter_program_decl(String name) throws HaltScanException {}

	public void enter_property(String name) {}

	
	public void enter_sequence(String name) {}

	
	public void enter_struct_decl(String name, List<SVClassIfcModParam> params)
			throws HaltScanException {}

	
	public void enter_task_decl(String name, int attr,
			List<SVTaskFuncParam> params) throws HaltScanException {}

	
	public void import_statment(String imp) throws HaltScanException {}

	
	public void leave_class_decl() throws HaltScanException {}

	
	public void leave_covergroup() {}
	
	public void constraint(String name, String expr) {}

	public void leave_func_decl() {}

	
	public void leave_interface_decl() {}

	
	public void leave_module_decl() throws HaltScanException {}

	
	public void leave_program_decl() throws HaltScanException {}


	public void leave_property() {}

	
	public void leave_sequence() {}

	
	public void leave_struct_decl(String name) {}

	
	public void leave_task_decl() {}
	
	public void typedef(String typeName, SVTypeInfo typeInfo) {}

	public void variable_decl(SVTypeInfo type, int attr, List<SvVarInfo> variables)
			throws HaltScanException {}

}
