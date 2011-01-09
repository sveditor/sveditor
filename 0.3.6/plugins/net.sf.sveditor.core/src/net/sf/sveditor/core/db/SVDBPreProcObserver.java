/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


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
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.PackageDecl) {
			setEndLocation(fScopeStack.peek());
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
		// Prevent the root scope from being removed
		if (fScopeStack.size() > 0 && fScopeStack.peek() instanceof SVDBPreProcCond) {
			fScopeStack.pop();
		}
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
		
		it.setLocation(new SVDBLocation(loc.getLineNo(), loc.getLinePos()));
	}
	
	private void setEndLocation(SVDBScopeItem item) {
		ScanLocation loc = fScanner.getStmtLocation();
		item.setEndLocation(new SVDBLocation(loc.getLineNo(), loc.getLinePos()));
	}
	
	public void error(String msg, String filename, int lineno, int linepos) {
		// Ignore errors in the pre-processor stage
		// System.out.println("[ERROR] " + msg);
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
			throws HaltScanException {
		SVDBModIfcClassDecl id = new SVDBModIfcClassDecl(
				name, SVDBItemType.Interface);
		fScopeStack.peek().addItem(id);
		fScopeStack.push(id);
		
		setLocation(id);
	}

	public void leave_interface_decl() {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Interface) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}
	
	public void enter_module_decl(String name, String ports)
			throws HaltScanException {
		SVDBModIfcClassDecl md = new SVDBModIfcClassDecl(
				name, SVDBItemType.Module);
		fScopeStack.peek().addItem(md);
		fScopeStack.push(md);

		setLocation(md);
	}

	public void leave_module_decl() throws HaltScanException {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Module) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void enter_program_decl(String name) throws HaltScanException {
		SVDBModIfcClassDecl p = new SVDBModIfcClassDecl(name, SVDBItemType.Program);
		
		fScopeStack.peek().addItem(p);
		fScopeStack.push(p);
		
		setLocation(p);
	}

	public void leave_program_decl() throws HaltScanException {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Program) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

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
	
	public void enter_initial_always_block(String id, String expr) {}

	public void leave_initial_always_block(String name) {}
	
	public void assign_stmt(String target) {}


	public void leave_property() {}

	
	public void leave_sequence() {}

	
	public void leave_struct_decl(String name) {}

	
	public void leave_task_decl() {}
	
	public void typedef(String typeName, SVTypeInfo typeInfo) {}

	public void variable_decl(SVTypeInfo type, int attr, List<SvVarInfo> variables)
			throws HaltScanException {}

}
