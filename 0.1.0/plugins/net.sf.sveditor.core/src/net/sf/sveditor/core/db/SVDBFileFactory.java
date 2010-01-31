package net.sf.sveditor.core.db;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.scanner.HaltScanException;
import net.sf.sveditor.core.scanner.IDefineProvider;
import net.sf.sveditor.core.scanner.ISVScanner;
import net.sf.sveditor.core.scanner.ISVScannerObserver;
import net.sf.sveditor.core.scanner.SVClassIfcModParam;
import net.sf.sveditor.core.scanner.SVEnumVal;
import net.sf.sveditor.core.scanner.SVScanner;
import net.sf.sveditor.core.scanner.SVTaskFuncParam;
import net.sf.sveditor.core.scanner.SVTypeInfo;
import net.sf.sveditor.core.scanner.SvVarInfo;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class SVDBFileFactory implements ISVScannerObserver {
	private SVScanner						fScanner;
	private SVDBFile						fFile;
	private Stack<SVDBScopeItem>			fScopeStack;

	public SVDBFileFactory() {
		fScanner = new SVScanner();
		fScanner.setObserver(this);
		fScopeStack = new Stack<SVDBScopeItem>();
	}

	public SVDBFileFactory(IDefineProvider def_provider) {
		this();
		setDefineProvider(def_provider);
	}
	
	public void setDefineProvider(IDefineProvider dp) {
		fScanner.setDefineProvider(dp);
	}
	
	public SVScanner getScanner() {
		return fScanner;
	}
	
	public void error(String msg) {
		System.out.println("[ERROR] " + msg);
	}
	
	public SVDBFile parse(InputStream in, String name) {
		fScopeStack.clear();
		
		fFile = new SVDBFile(name);
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
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.PackageDecl) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
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
	
	
	public void enter_program_decl(String name) throws HaltScanException {
		SVDBProgramBlock p = new SVDBProgramBlock(name);
		
		fScopeStack.peek().addItem(p);
		fScopeStack.push(p);
		
		setLocation(p);
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
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Interface) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	
	public void enter_class_decl(
			String 						name, 
			List<SVClassIfcModParam> 	params,
			String						super_name,
			List<SVClassIfcModParam>	super_params) 
		throws HaltScanException {
		SVDBModIfcClassDecl decl = new SVDBModIfcClassDecl(
				name, SVDBItemType.Class);
		
		for (SVClassIfcModParam p : params) {
			decl.getParameters().add(new SVDBModIfcClassParam(p.getName()));
		}
		
		decl.setSuperClass(super_name);
		
		if (super_params != null) {
			for (SVClassIfcModParam p : super_params) {
				decl.getSuperParameters().add(new SVDBModIfcClassParam(p.getName()));
			}
		}
		
		fScopeStack.peek().addItem(decl);
		fScopeStack.push(decl);
		
		setLocation(decl);
	}

	
	public void leave_class_decl() throws HaltScanException {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Class) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	
	public void enter_struct_decl(String name, List<SVClassIfcModParam> params) 
		throws HaltScanException {
		SVDBModIfcClassDecl decl = new SVDBModIfcClassDecl(
				name, SVDBItemType.Struct);
		
		fScopeStack.peek().addItem(decl);
		fScopeStack.push(decl);
		
		setLocation(decl);
	}

	public void leave_struct_decl(String name) throws HaltScanException {
		if (fScopeStack.size() > 0 &&
				fScopeStack.peek().getType() == SVDBItemType.Struct) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop().setName(name);
		}
	}

	
	public void enter_task_decl(
			String 						name,
			int 						attr,
			List<SVTaskFuncParam> 		params)
			throws HaltScanException {
		SVDBTaskFuncScope task = new SVDBTaskFuncScope(name, SVDBItemType.Task);
		task.setAttr(attr);
		
		for (SVTaskFuncParam p : params) {
			// TODO: fixme. Parameters can be of array/queue type too
			SVDBTypeInfo type_info = new SVDBTypeInfo(p.getTypeName(), 0);
			SVDBTaskFuncParam svp = new SVDBTaskFuncParam(type_info, p.getName());
			task.addParam(svp);
		}
		
		fScopeStack.peek().addItem(task);
		fScopeStack.push(task);
		
		setLocation(task);
	}
	
	public void enter_func_decl(
			String 						name,
			int 						attr,
			String						ret_type,
			List<SVTaskFuncParam> 		params)
			throws HaltScanException {
		SVDBTaskFuncScope func = new SVDBTaskFuncScope(name, SVDBItemType.Function);
		func.setAttr(attr);
		func.setReturnType(ret_type);
		
		for (SVTaskFuncParam p : params) {
			// TODO: fixme. Parameters can be of array/queue type too
			SVDBTypeInfo type_info = new SVDBTypeInfo(p.getTypeName(), 0);
			SVDBTaskFuncParam svp = new SVDBTaskFuncParam(type_info, p.getName());
			func.addParam(svp);
		}
		
		fScopeStack.peek().addItem(func);
		fScopeStack.push(func);
		
		setLocation(func);
	}

	
	public void leave_task_decl() {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Task) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void leave_func_decl() {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Function) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}
	
	public void enter_initial_always_block(String id, String expr) {
		SVDBScopeItem scope;
		if (id.equals("always")) {
			scope = new SVDBAlwaysBlock(expr);
		} else {
			scope = new SVDBInitialBlock();
		}
		setLocation(scope);
		
		fScopeStack.peek().addItem(scope);
		fScopeStack.push(scope);
	}
	
	public void leave_initial_always_block(String name) {
		if (fScopeStack.size() > 0 &&
				(fScopeStack.peek().getType() == SVDBItemType.AlwaysBlock ||
				 fScopeStack.peek().getType() == SVDBItemType.InitialBlock)) {
			setEndLocation(fScopeStack.peek());
			SVDBScopeItem scope = fScopeStack.pop();
			scope.setName(name);
		}
	}
	
	public void assign_stmt(String target) {
		SVDBAssign assign = new SVDBAssign(target);
		setLocation(assign);
		fScopeStack.peek().addItem(assign);
	}

	public void init(ISVScanner scanner) {
		// TODO Auto-generated method stub
		
	}

	
	public void leave_file() {
		if (fScopeStack.size() > 0 &&
				fScopeStack.peek().getType() == SVDBItemType.File) {
			setEndLocation(fScopeStack.peek());
		}
	}

	
	public void leave_module_decl() throws HaltScanException {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Module) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	
	public void leave_program_decl() throws HaltScanException {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Program) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}


	public void variable_decl(
			SVTypeInfo 		type, 
			int 			attr, 
			List<SvVarInfo>	variables) throws HaltScanException {
		
		if (type.fModIfc) {
			SVDBTypeInfo type_info = new SVDBTypeInfo(
					type.fTypeName, SVDBTypeInfo.TypeAttr_ModIfc);
			SVDBModIfcInstItem item = new SVDBModIfcInstItem(
					type_info, variables.get(0).fName);
			setLocation(item);
			fScopeStack.peek().addItem(item);
		} else {
			List<SVDBModIfcClassParam> parameters = null;
			
			if (type.fParameters != null) {
				parameters = new ArrayList<SVDBModIfcClassParam>();
				for (SVClassIfcModParam p : type.fParameters) {
					parameters.add(new SVDBModIfcClassParam(p.getName()));
				}
			}
			
			int type_attr = 0;
			
			if (type.fParameters != null && type.fParameters.size() > 0) {
				type_attr  |= SVDBTypeInfo.TypeAttr_Parameterized;
			}
			
			if (type.fVectorDim != null) {
				type_attr |= SVDBTypeInfo.TypeAttr_Vectored;
			}
				
			SVDBTypeInfo type_info = null;
			
			for (SvVarInfo var : variables) {
				if (var != null) {
					type_info = new SVDBTypeInfo(type.fTypeName, type_attr|var.fAttr);
					type_info.setArrayDim(var.fArrayDim);
					type_info.setVectorDim(type.fVectorDim);
					SVDBVarDeclItem item = new SVDBVarDeclItem(type_info, var.fName);
					setLocation(item);
					type_info.setParameters(parameters);
				
					if (item.getName() == null || item.getName().equals("")) {
						System.out.println("    " + item.getLocation().getFile().getName() + ":" + item.getLocation().getLine());
					}
					item.setAttr(attr);
					fScopeStack.peek().addItem(item);
				} else {
					// TODO: variable name is null
				}
			}
		}
	}

	public static SVDBFile createFile(InputStream in, String name) {
		return createFile(in, name, null);
	}

	public static SVDBFile createFile(
			InputStream 		in, 
			String 				name, 
			IDefineProvider		def_provider) {
		SVDBFileFactory f = new SVDBFileFactory(def_provider);
		
		return f.parse(in, name);
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
		SVDBMacroDef def = new SVDBMacroDef(key, params, value);
		
		setLocation(def);
		
		if (def.getName() == null || def.getName().equals("")) {
			System.out.println("    " + 
					def.getLocation().getFile().getName() + ":" + 
					def.getLocation().getLine());
		}
		
		fScopeStack.peek().addItem(def);
	}

	
	public void preproc_include(String path) {
		SVDBInclude inc = new SVDBInclude(path);
		
		setLocation(inc);
		fScopeStack.peek().addItem(inc);
	}
	
	public void enter_preproc_conditional(String type, String conditional) {}

	public void leave_preproc_conditional() {}


	public void comment(String comment) {
		
	}
	
	public void enter_covergroup(String name) {
		SVDBCoverGroup cg = new SVDBCoverGroup(name);
		setLocation(cg);
		
		fScopeStack.peek().addItem(cg);
		fScopeStack.push(cg);
	}

	
	public void leave_covergroup() {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Covergroup) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	
	public void covergroup_item(String name, String type, String target, String body) {
		SVDBItem it = null;
		
		if (type == null) {
			return;
		}

		if (type.equals("coverpoint")) {
			it = new SVDBCoverPoint(name, target, body);
		} else if (type.equals("cross")) {
			it = new SVDBCoverpointCross(name, body);
			
			for (String cp : target.split(",")) {
				cp = cp.trim();
				if (!cp.equals("")) {
					if (cp.endsWith(";")) {
						cp = cp.substring(0, cp.length()-1).trim();
					}
					((SVDBCoverpointCross)it).getCoverpointList().add(cp);
				}
			}
		} else {
//			System.out.println("unknown covergroup item: " + type);
		}
			
		if (it != null) {
			setLocation(it);
			fScopeStack.peek().addItem(it);
		}
	}
	
	public void constraint(String name, String expr) {
		SVDBConstraint c = new SVDBConstraint(name, expr);
		setLocation(c);
		fScopeStack.peek().addItem(c);
	}

	public void enter_sequence(String name) {
		SVDBScopeItem it = new SVDBScopeItem(name, SVDBItemType.Sequence);
		
		setLocation(it);
		fScopeStack.peek().addItem(it);
		fScopeStack.push(it);
	}

	
	public void leave_sequence() {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Sequence) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	
	public void enter_property(String name) {
		SVDBScopeItem it = new SVDBScopeItem(name, SVDBItemType.Property);
		
		setLocation(it);
		
		fScopeStack.peek().addItem(it);
		fScopeStack.push(it);
	}

	
	public void leave_property() {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Property) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void typedef(String typeName, SVTypeInfo typeInfo) {
		SVDBTypedef typedef;
		
		if (typeInfo.fEnumType) {
			typedef = new SVDBTypedef(typeName);
			
			for (SVEnumVal v : typeInfo.fEnumVals) {
				typedef.getEnumNames().add(v.fName);
				typedef.getEnumVals().add((int)v.fVal);
			}
		} else {
			typedef = new SVDBTypedef(typeInfo.fTypeName, typeName);
		}
		
		if (fScopeStack.size() > 0) {
			setLocation(typedef);
			fScopeStack.peek().addItem(typedef);
		}
	}
	
	

}
