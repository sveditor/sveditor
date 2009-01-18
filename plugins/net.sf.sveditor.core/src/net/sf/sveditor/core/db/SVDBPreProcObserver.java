package net.sf.sveditor.core.db;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.scanner.HaltScanException;
import net.sf.sveditor.core.scanner.ISVScanner;
import net.sf.sveditor.core.scanner.ISVScannerObserver;
import net.sf.sveditor.core.scanner.SVClassIfcModParam;
import net.sf.sveditor.core.scanner.SVTaskFuncParam;
import net.sf.sveditor.core.scanner.SVTypeInfo;
import net.sf.sveditor.core.scanner.ScanLocation;

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

	@Override
	public void init(ISVScanner scanner) {
		fScanner = scanner;
	}

	@Override
	public void enter_file(String filename) {
		SVDBFile file = new SVDBFile(new File(filename));
		fFileList.add(file);
		
		fScopeStack.push(file);
	}
	
	@Override
	public void enter_package(String name) {
		SVDBPackageDecl pd = new SVDBPackageDecl(name);
		setLocation(pd);
		fScopeStack.push(pd);
	}
	
	@Override
	public void leave_package() {
		if (fScopeStack.peek() instanceof SVDBPackageDecl) {
			fScopeStack.pop();
		}
	}
	
	@Override
	public void preproc_define(String key, List<String> params, String value) {
		SVDBMacroDef def = new SVDBMacroDef(key, params, value);
		setLocation(def);
		fFileList.get(fFileList.size()-1).getItems().add(def);
	}

	@Override
	public void preproc_include(String path) {
		SVDBInclude inc = new SVDBInclude(path);
		setLocation(inc);
		fScopeStack.peek().getItems().add(inc);
	}
	
	@Override
	public void leave_file() {
		fScopeStack.clear();
	}
	
	private void setLocation(SVDBItem it) {
		ScanLocation loc = fScanner.getStmtLocation();
		
		it.setLocation(new SVDBLocation(
				fFileList.get(fFileList.size()-1), 
				loc.getLineNo(), loc.getLinePos()));
	}
	
	@Override
	public void error(String msg) {
		System.out.println("[ERROR] " + msg);
	}


	@Override
	public void comment(String comment) {}

	@Override
	public void covergroup_item(String name, String type) {}

	@Override
	public void enter_class_decl(String name, List<SVClassIfcModParam> params,
			String super_name, List<SVClassIfcModParam> super_params)
			throws HaltScanException {}

	@Override
	public void enter_covergroup(String name) {}

	@Override
	public void enter_func_decl(String name, int attr, String ret_type,
			List<SVTaskFuncParam> params) throws HaltScanException {}

	@Override
	public void enter_interface_decl(String name, String ports)
			throws HaltScanException {}

	@Override
	public void enter_module_decl(String name, String ports)
			throws HaltScanException {}

	@Override
	public void enter_property(String name) {}

	@Override
	public void enter_sequence(String name) {}

	@Override
	public void enter_struct_decl(String name, List<SVClassIfcModParam> params)
			throws HaltScanException {}

	@Override
	public void enter_task_decl(String name, int attr,
			List<SVTaskFuncParam> params) throws HaltScanException {}

	@Override
	public void import_statment(String imp) throws HaltScanException {}

	@Override
	public void leave_class_decl() throws HaltScanException {}

	@Override
	public void leave_covergroup() {}

	@Override
	public void leave_func_decl() {}

	@Override
	public void leave_interface_decl() {}

	@Override
	public void leave_module_decl() throws HaltScanException {}

	@Override
	public void leave_property() {}

	@Override
	public void leave_sequence() {}

	@Override
	public void leave_struct_decl() {}

	@Override
	public void leave_task_decl() {}

	@Override
	public void variable_decl(SVTypeInfo type, int attr, List<String> variables)
			throws HaltScanException {}

}
