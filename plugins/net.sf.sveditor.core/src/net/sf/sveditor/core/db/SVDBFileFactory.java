package net.sf.sveditor.core.db;

import java.io.File;
import java.io.InputStream;
import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.parser.HaltScanException;
import net.sf.sveditor.core.parser.IDefineProvider;
import net.sf.sveditor.core.parser.ISVScanner;
import net.sf.sveditor.core.parser.ISVScannerObserver;
import net.sf.sveditor.core.parser.SVClassIfcModParam;
import net.sf.sveditor.core.parser.SVScanner;
import net.sf.sveditor.core.parser.SVTaskFuncParam;
import net.sf.sveditor.core.parser.ScanLocation;

public class SVDBFileFactory implements ISVScannerObserver, IDefineProvider {
	private SVScanner				fScanner;
	private SVDBFile				fFile;
	private Stack<SVDBScopeItem>	fScopeStack;
	
	private SVDBFileFactory() {
		fScanner = new SVScanner();
		fScanner.setObserver(this);
		fScanner.setDefineProvider(this);
		fScopeStack = new Stack<SVDBScopeItem>();
	}
	
	@Override
	public void error(String msg) {
		System.out.println("[ERROR] " + msg);
	}

	public SVDBFile parse(InputStream in, String name) {
		fScopeStack.clear();
		
		fFile = new SVDBFile(new File(name));
		fScopeStack.push(fFile);
		fScanner.scan(in, name);
		
		return fFile;
	}
	
	@Override
	public void enter_file(String filename) {
	}
	
	@Override
	public void import_statment(String imp) throws HaltScanException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void enter_module_decl(String name, String ports)
			throws HaltScanException {
		SVDBModIfcClassDecl md = new SVDBModIfcClassDecl(
				name, SVDBItemType.Module);
		fScopeStack.peek().addItem(md);
		fScopeStack.push(md);

		setLocation(md);
	}
	
	@Override
	public void enter_interface_decl(String name, String ports)
			throws HaltScanException {
		SVDBModIfcClassDecl id = new SVDBModIfcClassDecl(
				name, SVDBItemType.Interface);
		fScopeStack.peek().addItem(id);
		fScopeStack.push(id);
		
		setLocation(id);
	}

	@Override
	public void leave_interface_decl() {
		fScopeStack.pop();
	}

	@Override
	public void enter_class_decl(String name, List<SVClassIfcModParam> params) 
		throws HaltScanException {
		SVDBModIfcClassDecl decl = new SVDBModIfcClassDecl(
				name, SVDBItemType.Class);
		
		for (SVClassIfcModParam p : params) {
			decl.getParameters().add(new SVDBModIfcClassParam(p.getName()));
		}
		
		fScopeStack.peek().addItem(decl);
		fScopeStack.push(decl);
		
		setLocation(decl);
	}

	@Override
	public void leave_class_decl() throws HaltScanException {
		fScopeStack.pop();
	}

	@Override
	public void enter_task_decl(String name, int attr, List<SVTaskFuncParam> params)
			throws HaltScanException {
		SVDBTaskFuncScope task = new SVDBTaskFuncScope(name, SVDBItemType.Task);
		task.setAttr(attr);
		
		for (SVTaskFuncParam p : params) {
			SVDBTaskFuncParam svp = new SVDBTaskFuncParam(
					p.getTypeName(), p.getName());
			task.addParam(svp);
		}
		
		fScopeStack.peek().addItem(task);
		fScopeStack.push(task);
		
		setLocation(task);
	}

	@Override
	public void leave_task_decl() {
		fScopeStack.pop();
	}

	@Override
	public void init(ISVScanner scanner) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void leave_file() {
	}

	@Override
	public void leave_module_decl() throws HaltScanException {
		fScopeStack.pop();
	}


	@Override
	public void variable_decl(String type, int attr, List<String> variables)
			throws HaltScanException {
		for (String var : variables) {
			SVDBVarDeclItem item = new SVDBVarDeclItem(type, var);
			setLocation(item);
			item.setAttr(attr);
			fScopeStack.peek().addItem(item);
		}
	}

	public static SVDBFile createFile(InputStream in, String name) {
		SVDBFileFactory f = new SVDBFileFactory();
		
		return f.parse(in, name);
	}
	
	private void setLocation(SVDBItem item) {
		ScanLocation loc = fScanner.getStmtLocation();
		item.setLocation(new SVDBLocation(null, loc.getLineNo(), loc.getLinePos()));
	}

	@Override
	public void preproc_define(String key, List<String> params, String value) {
		System.out.println("key=" + key + " value=" + value);
		fFile.getMacroDefs().add(new SVDBMacroDef(key, params, value));
	}

	@Override
	public void preproc_include(String path) {
		fFile.getIncludes().add(path);
		
		// TODO: search path to see if we can locate 
	}

	@Override
	public String getDefineVal(String key, List<String> params) {
		System.out.println("getDefineVal: " + key);
		for (SVDBMacroDef d : fFile.getMacroDefs()) {
			if (d.getName().equals(key)) {
				System.out.println("def=" + d.getDef());
				return d.getDef();
			}
		}
		
		return null;
	}
	
}
