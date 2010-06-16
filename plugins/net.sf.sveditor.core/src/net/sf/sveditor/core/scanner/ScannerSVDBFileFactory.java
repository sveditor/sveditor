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


package net.sf.sveditor.core.scanner;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import net.sf.sveditor.core.BuiltinClassConstants;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.SVDBAlwaysBlock;
import net.sf.sveditor.core.db.SVDBAssign;
import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.SVDBCoverGroup;
import net.sf.sveditor.core.db.SVDBCoverPoint;
import net.sf.sveditor.core.db.SVDBCoverpointCross;
import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBInitialBlock;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBParamValueAssign;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.SVDBProgramBlock;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.SVDBTypedef;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.scanutils.ScanLocation;

public class ScannerSVDBFileFactory implements ISVScannerObserver, ISVDBFileFactory {
	private SVScanner						fScanner;
	private SVDBFile						fFile;
	private Stack<SVDBScopeItem>			fScopeStack;

	public ScannerSVDBFileFactory(IDefineProvider def_provider) {
		fScanner = new SVScanner();
		fScanner.setObserver(this);
		fScopeStack = new Stack<SVDBScopeItem>();
		if (def_provider != null) {
			System.out.println("[NOTE] define_provider not null. " + 
					def_provider.isDefined("ENABLE_CLASS1", -1));
			setDefineProvider(def_provider);
		} else {
			System.out.println("[NOTE] define_provider is null. "); 
		}
	}
	
	public void setDefineProvider(IDefineProvider dp) {
		fScanner.setDefineProvider(dp);
	}
	
	public SVScanner getScanner() {
		return fScanner;
	}
	
	public void error(String msg, String filename, int lineno) {
		SVDBMarkerItem marker = new SVDBMarkerItem(
				SVDBMarkerItem.MARKER_ERR,
				SVDBMarkerItem.KIND_GENERIC, msg);
		marker.setLocation(new SVDBLocation(lineno, 0));
		
		fFile.addItem(marker);
	}
	
	public SVDBFile parse(InputStream in, String name) {
		fScopeStack.clear();


		fFile = new SVDBFile(name);
		fScopeStack.push(fFile);
		fScanner.scan(in, name);
		
		return fFile;
	}
	
	public void init(InputStream in, String filename) {
		throw new RuntimeException("Test-only method");
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
			SVDBModIfcClassParam p_svdb = new SVDBModIfcClassParam(p.getName());
			p_svdb.setDefault(p.getDefault());
			decl.getParameters().add(p_svdb);
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
			SVDBTypeInfo type_info = new SVDBTypeInfoBuiltin(p.getTypeName());
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
		SVDBTaskFuncScope func = new SVDBTaskFuncScope(
				name, new SVDBTypeInfoBuiltin(ret_type));
		func.setAttr(attr);
		
		for (SVTaskFuncParam p : params) {
			// TODO: fixme. Parameters can be of array/queue type too
			SVDBTypeInfo type_info = new SVDBTypeInfoBuiltin(p.getTypeName());
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
			SVDBTypeInfo type_info = new SVDBTypeInfoUserDef(
					type.fTypeName, SVDBDataType.ModuleIfc);
			SVDBModIfcInstItem item = new SVDBModIfcInstItem(
					type_info, variables.get(0).fName);
			setLocation(item);
			fScopeStack.peek().addItem(item);
		} else {
			SVDBParamValueAssignList parameters = null;
			
			if (type.fParameters != null) {
				parameters = new SVDBParamValueAssignList();

				for (SVClassIfcModParam p : type.fParameters) {
					parameters.addParameter(
							new SVDBParamValueAssign("", p.getName()));
				}
			}
			
			int type_attr = 0;
			
			if (type.fVectorDim != null) {
				type_attr |= SVDBTypeInfo.TypeAttr_Vectored;
			}
				
			SVDBTypeInfo type_info = null;
			
			for (SvVarInfo var : variables) {
				if (var != null) {
					String typename = type.fTypeName;
					if (typename.indexOf('[') != -1) {
						typename = typename.substring(0, typename.indexOf('[')).trim();
					}
					if (SVKeywords.isBuiltInType(typename)) {
						SVDBTypeInfoBuiltin bi_type = new SVDBTypeInfoBuiltin(
								type.fTypeName);
						bi_type.setVectorDim(type.fVectorDim);
						type_info = bi_type;
					} else {
						SVDBTypeInfoUserDef ud_type = new SVDBTypeInfoUserDef(
								type.fTypeName, SVDBDataType.UserDefined);
						if (parameters != null) {
							ud_type.setParameters(parameters);
						}
						type_info = ud_type;
					}
					
					// type_info = new SVDBTypeInfo(type.fTypeName, type_attr|var.fAttr);
					SVDBVarDeclItem item = new SVDBVarDeclItem(type_info, var.fName, var.fAttr);
					item.setArrayDim(var.fArrayDim);
					setLocation(item);
				
					if (item.getName() == null || item.getName().equals("")) {
						System.out.println("    <<UNKNOWN>>:" + item.getLocation().getLine());
					}
					item.setAttr(attr);
					fScopeStack.peek().addItem(item);
				} else {
					// TODO: variable name is null
				}
			}
		}
	}

	private void setStartLocation(SVDBItem item) {
		ScanLocation loc = fScanner.getStartLocation();
		
		if (loc != null) {
			item.setLocation(new SVDBLocation(loc.getLineNo(), loc.getLinePos()));
		}
	}
	
	private void setLocation(SVDBItem item) {
		ScanLocation loc = fScanner.getStmtLocation();
		item.setLocation(new SVDBLocation(loc.getLineNo(), loc.getLinePos()));
	}
	
	private void setEndLocation(SVDBScopeItem item) {
		ScanLocation loc = fScanner.getStmtLocation();
		item.setEndLocation(new SVDBLocation(loc.getLineNo(), loc.getLinePos()));
	}

	
	public void preproc_define(String key, List<String> params, String value) {
		SVDBMacroDef def = new SVDBMacroDef(key, params, value);
		
		setLocation(def);
		
		if (def.getName() == null || def.getName().equals("")) {
			System.out.println("    :" + def.getLocation().getLine());
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
		cg.setSuperClass(BuiltinClassConstants.Covergroup);
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
		SVDBScopeItem it = null;
		
		if (type == null) {
			return;
		}

		if (type.equals("coverpoint")) {
			it = new SVDBCoverPoint(name, target, body);
			((SVDBCoverPoint)it).setSuperClass(BuiltinClassConstants.Coverpoint);
		} else if (type.equals("cross")) {
			it = new SVDBCoverpointCross(name, body);

			((SVDBCoverpointCross)it).setSuperClass(BuiltinClassConstants.CoverpointCross);

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
			setStartLocation(it);
			setEndLocation(it);
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
			SVDBTypeInfoEnum type = new SVDBTypeInfoEnum(typeName);
			
			for (SVEnumVal v : typeInfo.fEnumVals) {
				type.addEnumValue(v.fName, "" + v.fVal);
			}
			typedef = new SVDBTypedef(type, typeName);
		} else {
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(typeInfo.fTypeName);
			typedef = new SVDBTypedef(type, typeName);
		}
		
		if (fScopeStack.size() > 0) {
			setLocation(typedef);
			fScopeStack.peek().addItem(typedef);
		}
	}
	
	

}
