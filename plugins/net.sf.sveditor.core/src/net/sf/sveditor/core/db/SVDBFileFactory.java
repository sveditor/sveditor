package net.sf.sveditor.core.db;

import java.io.File;
import java.io.InputStream;
import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.ISVDBFileProvider;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVDBProjectDataFileProvider;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.scanner.HaltScanException;
import net.sf.sveditor.core.scanner.IDefineProvider;
import net.sf.sveditor.core.scanner.ISVScanner;
import net.sf.sveditor.core.scanner.ISVScannerObserver;
import net.sf.sveditor.core.scanner.SVClassIfcModParam;
import net.sf.sveditor.core.scanner.SVScanner;
import net.sf.sveditor.core.scanner.SVTaskFuncParam;
import net.sf.sveditor.core.scanner.ScanLocation;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;

public class SVDBFileFactory implements ISVScannerObserver, IDefineProvider {
	private SVScanner						fScanner;
	private SVDBFile						fFile;
	private Stack<SVDBScopeItem>			fScopeStack;
	private ISVDBFileProvider				fFileProvider;
	
	private SVDBFileFactory() {
		fScanner = new SVScanner();
		fScanner.setObserver(this);
		fScanner.setDefineProvider(this);
		fScopeStack = new Stack<SVDBScopeItem>();
	}
	
	
	public void error(String msg) {
		System.out.println("[ERROR] " + msg);
	}
	
	public SVDBFile parse(IFile file) {
		SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
		
		SVDBProjectData pdata = mgr.getProjectData(file.getProject());

		InputStream in = null;
		
		try {
			in = file.getContents();
		} catch (CoreException e) {
			e.printStackTrace();
		}
		
		return parse(in, file.getFullPath().toOSString(), 
				new SVDBProjectDataFileProvider(pdata));
	}
	
	public SVDBFile parse(InputStream in, String name) {
		return parse(in, name, null);
	}

	public SVDBFile parse(InputStream in, String name, ISVDBFileProvider file_p) {
		fFileProvider = file_p;
		
		fScopeStack.clear();
		
		fFile = new SVDBFile(new File(name));
		fScopeStack.push(fFile);
		fScanner.scan(in, name);
		
		return fFile;
	}
	
	
	public void enter_file(String filename) {
	}
	
	
	public void enter_package(String name) {
		SVDBPackageDecl pkg_decl = new SVDBPackageDecl(name);
		
		setLocation(pkg_decl);

		fScopeStack.peek().addItem(pkg_decl);
		fScopeStack.push(pkg_decl);
	}

	
	public void leave_package() {
		fScopeStack.pop();
	}

	
	public void import_statment(String imp) throws HaltScanException {
		// TODO Auto-generated method stub
		
	}

	
	public void enter_module_decl(String name, String ports)
			throws HaltScanException {
		SVDBModIfcClassDecl md = new SVDBModIfcClassDecl(
				name, SVDBItemType.Module);
		fScopeStack.peek().addItem(md);
		fScopeStack.push(md);

		setLocation(md);
	}
	
	
	public void enter_interface_decl(String name, String ports)
			throws HaltScanException {
		SVDBModIfcClassDecl id = new SVDBModIfcClassDecl(
				name, SVDBItemType.Interface);
		fScopeStack.peek().addItem(id);
		fScopeStack.push(id);
		
		setLocation(id);
	}

	
	public void leave_interface_decl() {
		setEndLocation(fScopeStack.peek());
		fScopeStack.pop();
	}

	
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

	
	public void leave_class_decl() throws HaltScanException {
		setEndLocation(fScopeStack.peek());
		fScopeStack.pop();
	}

	
	public void enter_struct_decl(String name, List<SVClassIfcModParam> params) 
		throws HaltScanException {
		SVDBModIfcClassDecl decl = new SVDBModIfcClassDecl(
				name, SVDBItemType.Struct);
		
		fScopeStack.peek().addItem(decl);
		fScopeStack.push(decl);
		
		setLocation(decl);
	}

	
	public void leave_struct_decl() throws HaltScanException {
		setEndLocation(fScopeStack.peek());
		fScopeStack.pop();
	}

	
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

	
	public void leave_task_decl() {
		setEndLocation(fScopeStack.peek());
		fScopeStack.pop();
	}

	
	public void init(ISVScanner scanner) {
		// TODO Auto-generated method stub
		
	}

	
	public void leave_file() {
	}

	
	public void leave_module_decl() throws HaltScanException {
		setEndLocation(fScopeStack.peek());
		fScopeStack.pop();
	}


	
	public void variable_decl(String type, int attr, List<String> variables)
			throws HaltScanException {
		
		if (type.startsWith(ISVScannerObserver.ModIfcInstPref)) {
			SVDBModIfcInstItem item = new SVDBModIfcInstItem(
					type.substring(ISVScannerObserver.ModIfcInstPref.length()),
					variables.get(0));
			setLocation(item);
			fScopeStack.peek().addItem(item);
		} else {
			for (String var : variables) {
				SVDBVarDeclItem item = new SVDBVarDeclItem(type, var);
				setLocation(item);
				item.setAttr(attr);
				fScopeStack.peek().addItem(item);
			}
		}
	}

	public static SVDBFile createFile(InputStream in, String name) {
		return createFile(in, name, null);
	}

	public static SVDBFile createFile(
			InputStream in, 
			String name, 
			ISVDBFileProvider file_provider) {
		SVDBFileFactory f = new SVDBFileFactory();
		
		return f.parse(in, name, file_provider);
	}

	private void setLocation(SVDBItem item) {
		ScanLocation loc = fScanner.getStmtLocation();
		item.setLocation(new SVDBLocation(fFile, loc.getLineNo(), loc.getLinePos()));
	}
	
	private void setEndLocation(SVDBScopeItem item) {
		ScanLocation loc = fScanner.getStmtLocation();
		item.setEndLocation(new SVDBLocation(null, loc.getLineNo(), loc.getLinePos()));
	}

	
	public void preproc_define(String key, List<String> params, String value) {
//		System.out.println("key=" + key + " value=" + value);
		SVDBMacroDef def = new SVDBMacroDef(key, params, value);
		
		setLocation(def);
		
		fFile.addItem(def);
	}

	
	public void preproc_include(String path) {
		SVDBInclude inc = new SVDBInclude(path);
		
		setLocation(inc);
		fScopeStack.peek().addItem(inc);
		
		// See if we can locate the file...
		SVDBFile file = null;
		if (fFileProvider != null) {
			file = fFileProvider.getFile(path);
		}
		
		if (file != null) {
			fFile.addFileRef(file);
		}
	}

	
	public String getDefineVal(String key, List<String> params) {
//		System.out.println("getDefineVal: " + key);
		
		SVDBMacroDef def = fFile.getMacroDef(key);
		
		if (def != null) {
			/*
			System.out.println("preproc define \"" + 
					def.getName() + "\" from file \"" + 
					def.getLocation().getFile().getName() + "\"");
             */
			return def.getDef();
		} else {
			return null;
		}
	}
	
	public boolean hasParameters(String key) {
		SVDBMacroDef def;
		
		if ((def = fFile.getMacroDef(key)) != null) {
			return (def.getParameters().size() > 0);
		}
		
		return false;
	}


	public void enter_covergroup(String name) {
		SVDBCoverGroup cg = new SVDBCoverGroup(name);
		setLocation(cg);
		
		fScopeStack.peek().addItem(cg);
		fScopeStack.push(cg);
	}

	
	public void leave_covergroup() {
		fScopeStack.pop();
	}

	
	public void covergroup_item(String name, String type) {
		SVDBItem it = null;
		
		if (type == null) {
			return;
		}
		
		if (type.equals("coverpoint")) {
			it = new SVDBItem(name, SVDBItemType.Coverpoint);
		} else {
			System.out.println("unknown covergroup item: " + type);
		}
			
		if (it != null) {
			setLocation(it);
			fScopeStack.peek().addItem(it);
		}
	}

	
	public void enter_sequence(String name) {
		SVDBScopeItem it = new SVDBScopeItem(name, SVDBItemType.Sequence);
		
		setLocation(it);
		fScopeStack.peek().addItem(it);
		fScopeStack.push(it);
	}

	
	public void leave_sequence() {
		fScopeStack.pop();
	}

	
	public void enter_property(String name) {
		SVDBScopeItem it = new SVDBScopeItem(name, SVDBItemType.Property);
		
		setLocation(it);
		
		fScopeStack.peek().addItem(it);
		fScopeStack.push(it);
	}

	
	public void leave_property() {
		fScopeStack.pop();
	}

}
