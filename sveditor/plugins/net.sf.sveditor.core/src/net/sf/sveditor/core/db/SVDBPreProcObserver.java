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

import net.sf.sveditor.core.scanner.ISVPreProcScannerObserver;
import net.sf.sveditor.core.scanner.ISVScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVDBPreProcObserver implements ISVPreProcScannerObserver {
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
		fScopeStack.peek().addItem(inc);
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

	public void enter_interface_decl(String name, String ports) {
		SVDBModIfcDecl id = new SVDBModIfcDecl(
				name, SVDBItemType.InterfaceDecl);
		fScopeStack.peek().addItem(id);
		fScopeStack.push(id);
		
		setLocation(id);
	}

	public void leave_interface_decl() {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.InterfaceDecl) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}
	
	public void enter_module_decl(String name, String ports) {
		SVDBModIfcDecl md = new SVDBModIfcDecl(
				name, SVDBItemType.ModuleDecl);
		fScopeStack.peek().addItem(md);
		fScopeStack.push(md);

		setLocation(md);
	}

	public void leave_module_decl() {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.ModuleDecl) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void enter_program_decl(String name) {
		SVDBModIfcDecl p = new SVDBModIfcDecl(name, SVDBItemType.ProgramDecl);
		
		fScopeStack.peek().addItem(p);
		fScopeStack.push(p);
		
		setLocation(p);
	}

	public void leave_program_decl() {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.ProgramDecl) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

}
