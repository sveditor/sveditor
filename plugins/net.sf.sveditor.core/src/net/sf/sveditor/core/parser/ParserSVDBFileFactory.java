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


package net.sf.sveditor.core.parser;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import net.sf.sveditor.core.BuiltinClassConstants;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.SVDBAlwaysBlock;
import net.sf.sveditor.core.db.SVDBAssign;
import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.SVDBCoverGroup;
import net.sf.sveditor.core.db.SVDBCoverPoint;
import net.sf.sveditor.core.db.SVDBCoverpointCross;
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
import net.sf.sveditor.core.db.SVDBProgramBlock;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypedef;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.scanner.EOFException;
import net.sf.sveditor.core.scanner.HaltScanException;
import net.sf.sveditor.core.scanner.IDefineProvider;
import net.sf.sveditor.core.scanner.IPreProcErrorListener;
import net.sf.sveditor.core.scanner.ISVPreProcScannerObserver;
import net.sf.sveditor.core.scanner.ISVScanner;
import net.sf.sveditor.core.scanner.ISVScannerObserver;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanner.SVClassIfcModParam;
import net.sf.sveditor.core.scanner.SVEnumVal;
import net.sf.sveditor.core.scanner.SVKeywords;
import net.sf.sveditor.core.scanner.SVPreProcScanner;
import net.sf.sveditor.core.scanner.SVScannerTextScanner;
import net.sf.sveditor.core.scanner.SVTaskFuncParam;
import net.sf.sveditor.core.scanner.SVTypeInfo;
import net.sf.sveditor.core.scanner.SvVarInfo;
import net.sf.sveditor.core.scanner.VerilogNumberParser;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;
import net.sf.sveditor.core.scanutils.StringTextScanner;

/**
 * Scanner for SystemVerilog files. 
 *  
 * @author ballance
 *
 * - Handle structures
 * - Handle enum types
 * - Handle export/import, "DPI-C", context as function/task qualifiers
 * - type is always <type> <qualifier>, so no need to handle complex ordering
 *    (eg unsigned int)
 * - handle property as second-level scope
 * - recognize 'import'
 * - handle class declaration within module
 * - Handle sequence as empty construct
 */
public class ParserSVDBFileFactory 
	implements ISVScanner, IPreProcErrorListener, ISVDBFileFactory,
		ISVPreProcScannerObserver, ISVParser {
	private Stack<String>			fSemanticScopeStack;
	private SVScannerTextScanner	fInput;
	private SVLexer					fLexer;
	
	private boolean					fNewStatement;
	private ScanLocation			fStmtLocation;
	private ScanLocation			fStartLocation;
	
	private IDefineProvider			fDefineProvider;
	private boolean					fEvalConditionals = true;

	private SVDBFile				fFile;
	private Stack<SVDBScopeItem>	fScopeStack;
	private SVParsers				fSVParsers;

	
	public ParserSVDBFileFactory(IDefineProvider dp) {
		setDefineProvider(dp);
		fScopeStack = new Stack<SVDBScopeItem>();
		fSemanticScopeStack = new Stack<String>();
		fSVParsers = new SVParsers(this);
		
		if (dp != null) {
			setDefineProvider(dp);
		}
	}
	
	public void setDefineProvider(IDefineProvider p) {
		fDefineProvider = p;
	}
	
	public void setEvalConditionals(boolean eval) {
		fEvalConditionals = eval;
	}
	
	public ScanLocation getStmtLocation() {
		if (fStmtLocation == null) {
			// TODO: should fix, really
			return getLocation();
		}
		return fStmtLocation;
	}
	
	public ScanLocation getStartLocation() {
		return fStartLocation;
	}

	public void setStmtLocation(ScanLocation loc) {
		fStmtLocation = loc;
	}
	
	public void preProcError(String msg, String filename, int lineno) {
		error(msg, filename, lineno);
	}

	/**
	 * 
	 * @param in
	 */
	public void scan(InputStream in, String filename) {
	
		fNewStatement = true;
		
		if (fDefineProvider != null) {
			fDefineProvider.addErrorListener(this);
		}
		
		SVPreProcScanner pp = new SVPreProcScanner();
		pp.setDefineProvider(fDefineProvider);
		pp.setScanner(this);
		pp.setObserver(this);
		
		pp.init(in, filename);
		pp.setExpandMacros(true);
		pp.setEvalConditionals(fEvalConditionals);
		
		fInput = new SVScannerTextScanner(pp);
		fLexer = new SVLexer();
		fLexer.init(this);
		
		enter_file(filename);

		try {
			process();
		} catch (SVParseException e) {
			e.printStackTrace();
		}

		leave_file();
		
		if (fDefineProvider != null) {
			fDefineProvider.removeErrorListener(this);
		}
	}
	
	private void process() throws SVParseException {
		String id;
		
		try {
			while ((id = scan_statement()) != null) {
				Pair<String, Integer> ret = scan_qualifiers(id, false);
				id = ret.fField1;

				if (id != null) {
					if (id.equals("class")) {
						SVDBModIfcClassDecl cls = null;
						try {
							cls = parsers().classParser().parse(ret.fField2);
						} catch (SVParseException e) {
							e.printStackTrace();
						}
					} else if (id.equals("module") ||
							id.equals("interface") ||
							id.equals("program")) {
						// enter module scope
						process_interface_module_class(id);
					} else if (id.equals("struct")) {
						process_struct_decl(null);
					} else if (id.equals("package") || id.equals("endpackage")) {
						process_package(id);
					} else if (id.equals("import")) {
						process_import(id);
					} else if (id.equals("export")) {
						process_export(id);
					} else if (id.equals("typedef")) {
						process_typedef();
					} else if (id.equals("function") || id.equals("task")) {
						process_task_function(ret.fField2, id);
					}
				} else {
					System.out.println("[WARN] id @ top-level is null");
					System.out.println("    " + getLocation().getFileName() + 
							":" + getLocation().getLineNo());
				}
			}
		} catch (EOFException e) {
		}
	}
	
	private void process_initial_always(String id) throws EOFException {
		int ch = skipWhite(get_ch());
		String expr = "", name = "";
		String type = id;
		
		if (id.equals("always")) {
			if (ch == '@') {
				startCapture(ch);
				ch = skipWhite(get_ch());
				
				if (ch == '(') {
					ch = skipPastMatch("()");
				}
				expr = endCapture();
			} else if (ch == '#') {
				startCapture(ch);
				ch = skipWhite(get_ch());
				
				if (ch == '(') {
					ch = skipPastMatch("()");
				} else {
					// Just read to the end of the next whitespace item
					while ((ch = get_ch()) != -1 && !Character.isWhitespace(ch)) {}
				}
				
				expr = endCapture();
			}
			
		}
		
		ch = skipWhite(ch);
		
		id = readIdentifier(ch);
		
		enter_initial_always_block(type, expr);
		
		if (id != null && id.equals("begin")) {
			int begin_cnt = 1;
			int end_cnt = 0;
			boolean var_enabled = true;

			ch = skipWhite(get_ch());
			
			if (ch == ':') {
				// named begin
				ch = skipWhite(get_ch());
				
				if (SVCharacter.isSVIdentifierStart(ch)) {
					name = readIdentifier(ch);
				}
			} else {
				unget_ch(ch);
			}
			
			do {
				do {
					ch = skipWhite(get_ch());
				} while (ch != -1 && !SVCharacter.isSVIdentifierStart(ch));
				
				if ((id = readIdentifier(ch)) != null) {
					if (id.equals("begin")) {
						begin_cnt++;
					} else if (id.equals("end")) {
						end_cnt++;
					}
				}
			} while (id != null && begin_cnt != end_cnt);
		} else {
			// single-statement begin.
		}
		
		leave_initial_always_block(name);
	}
	
	private void process_assign() throws EOFException {
		int ch = skipWhite(get_ch());
		String target = "";

		if (ch == '(' || SVCharacter.isSVIdentifierStart(ch)) {
			target = readExpression(ch);
		} else if (ch == '{') {
			startCapture(ch);
			ch = skipPastMatch("{}");
			target = endCapture();
		}
		
		SVDBAssign assign = new SVDBAssign(target);
		setLocation(assign);
		fScopeStack.peek().addItem(assign);
	}
	
	private void process_constraint(String id) throws EOFException {
		int ch = get_ch();
		
		ch = skipWhite(ch);
		
		String cname = readIdentifier(ch);
		
		ch = skipWhite(get_ch());
		
		if (ch == '{') {
			startCapture();
			ch = skipPastMatch("{}");
			String expr = endCapture();
			
			expr = expr.substring(0, expr.length()-2);
			
			constraint(cname, expr);
		}
		
		fNewStatement = true;
	}
	
	private void process_covergroup(String id) throws EOFException {
		int ch = get_ch();
		
		
		fSemanticScopeStack.push("covergroup");
		
		
		ch = skipWhite(ch);
		
		String cg_name = readIdentifier(ch);

		enter_covergroup(cg_name);

		ch = skipWhite(get_ch());
		
		while (ch == '(') {
			ch = skipPastMatch("()");
		}
		
		if (ch == '@') {
			ch = skipWhite(get_ch());
			if (ch == '@') {
				ch = skipWhite(get_ch());
			}
			
			if (ch == '(') {
				ch = skipPastMatch("()");
			}
		}
		
		// Skip statements
		while ((id = scan_statement()) != null) {
			fStartLocation = getStmtLocation(); 
			
			if (id.equals("endgroup")) {
				break;
			} else {
				// This is likely a coverpoint/coverpoint cross 
				ch = skipWhite(get_ch());
				
				if (ch == ':') {
					// yep...
					ch = skipWhite(get_ch());
					String name = id;
					
					String type = readIdentifier(ch);
					
					// Now, skip forward and try to read the target
					ch = skipWhite(get_ch());
					
					// read any expression character
					startCapture(ch);
					while (ch != -1 && ch != '{' && ch != ';') {
						ch = get_ch();
					}
					String target = endCapture();
					
					if (target != null) {
						if (target.endsWith("{")) {
							target = target.substring(0, target.length()-1);
						}
						target = target.trim();
					}
					
					
					ch = skipWhite(ch);

					String body = "";
					if (ch == '{') {
						startCapture();
						skipPastMatch("{}");
						body = endCapture();
						
						body = body.trim();
						if (body.endsWith("}")) {
							body = body.substring(0, body.length()-1);
						}
					}
					
					// Update the end location
					setStmtLocation(getLocation());
					covergroup_item(name, type, target, body);
					fNewStatement = true;
				}
			}
		}
		
		handle_leave_scope();
	}
	
	private void process_sequence(String id) throws EOFException {
		
		int ch = skipWhite(get_ch());
		
		String name = readIdentifier(ch);
		fSemanticScopeStack.push("sequence");
		
		enter_sequence(name);
		
		while ((id = scan_statement()) != null) {
			if (id.equals("endsequence")) {
				break;
			}
		}
		
		handle_leave_scope();
	}
	
	private SVDBItem process_property(String id) throws EOFException {
		int ch = skipWhite(get_ch());
		
		String name = readIdentifier(ch);
		fSemanticScopeStack.push("property");
		
		SVDBScopeItem it = new SVDBScopeItem(name, SVDBItemType.Property);
		
		setLocation(it);
		
		fScopeStack.peek().addItem(it);
		fScopeStack.push(it);
		
		while ((id = scan_statement()) != null) {
			if (id.equals("endproperty")) {
				break;
			}
		}
		
		handle_leave_scope();
		
		return it;
	}
	
	private class Pair <T1, T2> {
		T1			fField1;
		T2			fField2;
	}
	
	private Pair<String, Integer> scan_qualifiers(String id, boolean param) throws EOFException {
		Pair<String, Integer> ret = new Pair<String, Integer>();
		int modifiers = 0;
		Map<String, Integer>	qmap = (param)?fTaskFuncParamQualifiers:fFieldQualifers;
		
		ret.fField2 = 0;
		while (qmap.containsKey(id)) {
			debug("item modified by \"" + id + "\"");
			modifiers |= qmap.get(id);
			
			if (!lexer().next_token()) {
				break;
			}
			id = lexer().peek();
		}
		
		ret.fField1 = id;
		ret.fField2 = modifiers;
		
		return ret;
	}
	
	public String scopedIdentifier() throws SVParseException {
		StringBuilder id = new StringBuilder();
		
		id.append(lexer().readId());
		
		while (lexer().peekOperator("::")) {
			id.append("::");
			id.append(lexer().readId());
		}
		
		return id.toString();
	}
	
	private SVDBItem process_task_function(int modifiers, String id) throws SVParseException {
		// Scan for end-of-section
		String 						tf_name;
		String						ret_type = null;
		List<SVTaskFuncParam>		params = new ArrayList<SVTaskFuncParam>();
		SVDBTaskFuncScope			scope;
		debug("--> process_task_function \"" + id + "\"");
		int ch = skipWhite(get_ch());
		
		fSemanticScopeStack.push(id);
		
		// This could be:
		// task name
		// 'new'
		tf_name = lexer().readId();
		
		debug("    tf_name=" + tf_name);

		unget_ch(ch);
		Pair<String, Integer> mod_ret = scan_qualifiers(tf_name, false);
		ch = get_ch();

		tf_name    = mod_ret.fField1;
		modifiers |= mod_ret.fField2;

		debug("    tf_name=" + tf_name);
		
		if (id.equals("function")) {
			// could have a return type.
			unget_ch(ch);
			unget_str(tf_name + " ");
			ch = skipWhite(get_ch());
			SVTypeInfo typename = readTypeName(ch, false);
			ret_type = typename.fTypeName;
			ch = skipWhite(get_ch());
			
			if (ch == '(' || ch == ';') {
				// no return type
				tf_name = typename.fTypeName;
			} else {
				tf_name = readIdentifier(ch);
				ch = skipWhite(get_ch());
			}
		}
		
		debug("post-task \"" + tf_name + "\" ch=" + (char)ch);
		
		if (ch == '(') {
			SVTypeInfo t;
			String n;
			int cnt = 0;
			
			while (ch == '(') {
				ch = skipWhite(get_ch());
				cnt++;
			}
			
			debug("get_ch=" + (char)ch);
			
			do {
				ch = skipWhite(ch);

				if (ch == ';' || ch == ')') {
					break;
				}

				if ((t = readTypeName(ch, true)) == null) {
					break;
				}
			
				ch = get_ch();
				
				ch = skipWhite(ch);
				
				if (ch == ';' || ch == ')') {
					break;
				}
				
				// Should be name of 
				n = readIdentifier(ch);
				ch = get_ch();

				while (ch == '[') {
					startCapture(ch);
					ch = skipPastMatch("[]", ",;");
					
					String capture = endCapture();
					capture = capture.substring(0, capture.length()-1).trim();
					
					t.fArrayDim = capture;
					ch = skipWhite(ch);
				}
				
				SVTaskFuncParam p = new SVTaskFuncParam(t.fTypeName, n);
				params.add(p);
				
				ch = skipWhite(ch);

				if (ch == '=') {
					ch = skipWhite(get_ch());
					while (ch != -1 && ch != ',' && ch != ')' &&
							!Character.isWhitespace(ch)) {
						ch = get_ch();
					}
					ch = skipWhite(ch);
				}
				
				if (ch == ';' || ch == ')') {
					break;
				}
				
				ch = skipWhite(ch);
				if (ch == ',') {
					ch = skipWhite(get_ch());
				} else {
					break;
				}
			} while (t != null && ch != ')' && ch != -1);
		}
		
		if (ret_type != null) {
			scope = new SVDBTaskFuncScope(tf_name, SVDBItemType.Function);
			scope.setAttr(modifiers);
			scope.setReturnType(new SVDBTypeInfo(ret_type, 0));
			
			for (SVTaskFuncParam p : params) {
				// TODO: fixme. Parameters can be of array/queue type too
				SVDBTypeInfo type_info = new SVDBTypeInfo(p.getTypeName(), 0);
				SVDBTaskFuncParam svp = new SVDBTaskFuncParam(type_info, p.getName());
				scope.addParam(svp);
			}
			
			fScopeStack.peek().addItem(scope);
			fScopeStack.push(scope);
			
			setLocation(scope);
		} else {
			scope = new SVDBTaskFuncScope(tf_name, SVDBItemType.Task);
			scope.setAttr(modifiers);
			
			for (SVTaskFuncParam p : params) {
				// TODO: fixme. Parameters can be of array/queue type too
				SVDBTypeInfo type_info = new SVDBTypeInfo(p.getTypeName(), 0);
				SVDBTaskFuncParam svp = new SVDBTaskFuncParam(type_info, p.getName());
				scope.addParam(svp);
			}
			
			fScopeStack.peek().addItem(scope);
			fScopeStack.push(scope);
			
			setLocation(scope);
		}
		
		debug("" + id + " " + tf_name);
		
		boolean has_body = true;
		
		if ((modifiers & ISVScannerObserver.FieldAttr_Extern) != 0 ||
				((modifiers & ISVScannerObserver.FieldAttr_Pure) != 0 &&
				 (modifiers & ISVScannerObserver.FieldAttr_Virtual) != 0) ||
				(modifiers & ISVScannerObserver.FieldAttr_DPI) != 0) {
			has_body = false;
		}
		
		// External tasks/functions don't have a body
		if ((modifiers & ISVScannerObserver.FieldAttr_Pure) != 0 &&
				(modifiers & ISVScannerObserver.FieldAttr_Virtual) != 0) {
			has_body = false;
		}
		
		if (has_body) {
			String  exp_end = "end" + id;
			if (!task_function_initial_body(exp_end)) {
				scope = null;
			}
		} else {
			debug("    extern task/function declaration");
		}
		
		handle_leave_scope();
		
		debug("--> process_task_function \"" + scope.getName() + "\"");
		return scope;
	}
	
	private boolean task_function_initial_body(String exp_end) throws SVParseException {
		boolean var_enabled = true;
		String id;
		boolean ret = true;
		
		while ((id = scan_statement()) != null) {
			// First, look for local variables
			if (var_enabled && !id.equals(exp_end)) {
				if (!SVKeywords.isSVKeyword(id) || SVKeywords.isBuiltInType(id)) {
					unget_str(id + " ");
					
					var_enabled = scanVariableDeclaration(0);
				} else {
					var_enabled = false;
				}
			} else if (id.equals(exp_end)) {
				break;
			} else if (isSecondLevelScope(id)) {
//				System.out.println("id \"" + id + "\" is a second-level scope");
				error("missing \"" + exp_end + "\"",
						getLocation().getFileName(),
						getLocation().getLineNo());

				// 
				fNewStatement = true;
				unget_str(id + " ");
				break;
			} else if (isFirstLevelScope(id, 0)) {
				error("missing \"" + exp_end + "\"",
						getLocation().getFileName(),
						getLocation().getLineNo());

				// We're in a first-level scope.
				// we pick it up on next pass
				handle_leave_scope();
				ret = false;
				fNewStatement = true;
				unget_str(id + " ");
				break;
			}
			debug("    behave section: " + id);
		}
		debug("    endbehave: " + id);
		
		return ret;
	}
	
	private SVDBItem process_interface_module_class(String type) throws SVParseException {
		SVDBItem it = null;
		String id;
		List<SVClassIfcModParam>	params = null;
		String super_name = null;
		List<SVClassIfcModParam>	super_params = null;
		String module_type_name = null;
		String ports = null;
		int ch = skipWhite(get_ch());
		
		debug("--> process_module()");

		fSemanticScopeStack.push(type);
		
		//
		// Skip up to point of module type name
		//
		
		ch = skipWhite(ch);
		
		if (SVCharacter.isSVIdentifierStart(ch)) {
			module_type_name = readIdentifier(ch);
			ch = get_ch();
			debug("  module_type_name=" + module_type_name);
		} else {
			return it;
		}

		// Handle modules with parameters
		ch = skipWhite(ch);
		if (ch == '#') {
			ch = skipWhite(get_ch());
			if (ch == '(') {
				startCapture();
				ch = skipPastMatch("()");
				String p_str = endCapture();
				
				params = parse_parameter_str(p_str);
			}
		}
		
		if (params == null) {
			params = new ArrayList<SVClassIfcModParam>();
		}
		
		// Class extension
		ch = skipWhite(ch);
		if (type.equals("class")) {
			if (SVCharacter.isSVIdentifierPart(ch)) {
				// likely an 'extends' statement
				String ext = readIdentifier(ch);
				
				ch = get_ch();
				if (ext != null) {
					if (ext.equals("extends")) {
						ch = skipWhite(ch);
						super_name = readIdentifier(ch);

						ch = skipWhite(get_ch());

						if (ch == '#') {
							// parameters
							ch = skipWhite(get_ch());
							if (ch == '(') {
								startCapture();
								ch = skipPastMatch("()");
								String p_str = endCapture();

								super_params = parse_parameter_str(p_str);
							}
						}
					}
				}
			} else if (ch != ';') {
				System.out.println("Mystery post-class character: \"" + (char)ch + "\"");
				System.out.println("    " + getLocation().getFileName() + ":" + 
						getLocation().getLineNo());
			}
		} else if (type.equals("module")) {
			// Module port-list
			if (ch == '(') {
				startCapture(ch);
				ch = skipPastMatch("()");
				ports = endCapture();
			}
		}
		ch = skipWhite(ch);
		unget_ch(ch);
		
		if (type.equals("module")) {
			SVDBModIfcClassDecl cls = 
				new SVDBModIfcClassDecl(module_type_name, SVDBItemType.Module);
			fScopeStack.peek().addItem(cls);
			fScopeStack.push(cls);

			setLocation(cls);
			it = cls;
		} else if (type.equals("program")) {
			SVDBProgramBlock p = new SVDBProgramBlock(module_type_name);
			
			fScopeStack.peek().addItem(p);
			fScopeStack.push(p);
			
			setLocation(p);
			it = p;
		} else if (type.equals("interface")) {
			SVDBModIfcClassDecl ifc = new SVDBModIfcClassDecl(
					module_type_name, SVDBItemType.Interface);
			fScopeStack.peek().addItem(ifc);
			fScopeStack.push(ifc);
			
			setLocation(ifc);
			it = ifc;
		} else if (type.equals("class")) {
			System.out.println("[ERROR] should not be calling enter_class_decl");
			SVDBModIfcClassDecl decl = new SVDBModIfcClassDecl(
					module_type_name, SVDBItemType.Class);
			
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
			it = decl;
		} else if (type.equals("struct")) {
			SVDBModIfcClassDecl decl = new SVDBModIfcClassDecl(
					module_type_name, SVDBItemType.Struct);
			
			fScopeStack.peek().addItem(decl);
			fScopeStack.push(decl);
			
			setLocation(decl);
		}

		while ((id = scan_statement()) != null) {
			debug("id=" + id);
			if (id.equals("end" + type)) {
				break;
			}
			SVDBItem item = process_module_class_interface_body_item(type, id);

			// Check whether we aborted parsing the body because
			// we found a 1st-level scope keyword
			if (item == null) {
				break;
			}
			
			// TODO: Should have already been added ?
			// fScopeStack.peek().addItem(item);
		}
		
		// Pop the first-level scope
		handle_leave_scope();
		
		debug("<-- process_module()");
		return it;
	}
	
	private void process_struct_decl(SVTypeInfo type_info) throws SVParseException {
		int ch = skipWhite(get_ch());
		
		System.out.println("process_struct_decl");
		
		while (SVCharacter.isSVIdentifierStart(ch)) {
			/* String qual = */ readIdentifier(ch);
			
			ch = skipWhite(get_ch());
		}
		
		if (ch != '{') {
			return;
		}

		// Add struct declaration
		SVDBModIfcClassDecl decl = new SVDBModIfcClassDecl(
				"", SVDBItemType.Struct);
		fScopeStack.peek().addItem(decl);
		fScopeStack.push(decl);
		setLocation(decl);
		
		
		String id;
		
		while ((id = scan_statement()) != null) {
			SVDBItem item = process_module_class_interface_body_item("struct", id);
			
			if (item == null) {
				break;
			}
			
			// Add the item to the struct declaration
			fScopeStack.peek().addItem(item);

			// Recognize when we've reached the end of the
			// struct definition
			ch = skipWhite(get_ch());
			
			if (ch == ';') {
				int ch2 = skipWhite(get_ch());
				if (ch2 == '}') {
					break;
				} else {
					unget_ch(ch2);
					unget_ch(ch);
				}
			}
		}
		
		if (type_info == null) {
			fStmtLocation = getLocation();
			leave_struct_decl("ANONYMOUS");
		}

		/*
		startCapture();
		ch = skipPastMatch("{}");
		endCapture();
		
		// TODO: 
		
		ch = skipWhite(ch);
		 */
	}
	
	private void process_package(String id) throws EOFException {
		if (id.equals("package")) {
			int ch = skipWhite(get_ch());
			String pkg = readQualifiedIdentifier(ch);
			enter_package(pkg);
		} else {
			leave_package();
		}
	}
	
	public void enter_scope(String type, SVDBScopeItem scope) {
		fSemanticScopeStack.push(type);
		fScopeStack.peek().addItem(scope);
	}
	
	public void handle_leave_scope() {
		handle_leave_scope(1);
	}
	
	private void handle_leave_scope(int levels) {
		fStmtLocation = getLocation();
		for (int i=0; i<levels; i++) {
			String type = null;
			
			if (fSemanticScopeStack.size() > 0) {
				type = fSemanticScopeStack.pop();
			} else {
				System.out.println("[ERROR] attempting to leave scope @ " + 
						getLocation().getFileName() + ":" +
						getLocation().getLineNo());
			}
			
			if (type != null) {
				if (type.equals("module")) {
					leave_module_decl();
				} else if (type.equals("program")) {
					leave_program_decl();
				} else if (type.equals("interface")) {
					leave_interface_decl();
				} else if (type.equals("class")) {
					leave_class_decl();
				} else if (type.equals("struct")) {
					leave_struct_decl("");
				} else if (type.equals("task")) {
					leave_task_decl();
				} else if (type.equals("function")) {
					leave_func_decl();
				} else if (type.equals("covergroup")) {
					leave_covergroup();
				} else if (type.equals("sequence")) {
					if (fScopeStack.size() > 0 && 
							fScopeStack.peek().getType() == SVDBItemType.Sequence) {
						setEndLocation(fScopeStack.peek());
						fScopeStack.pop();
					}
				} else if (type.equals("property")) {
					if (fScopeStack.size() > 0 && 
							fScopeStack.peek().getType() == SVDBItemType.Property) {
						setEndLocation(fScopeStack.peek());
						fScopeStack.pop();
					}
				}
			}
		}
	}
	
	private List<SVClassIfcModParam> parse_parameter_str(String p_str) {
		List<SVClassIfcModParam> ret = new ArrayList<SVClassIfcModParam>();
		ITextScanner in = new StringTextScanner(new StringBuilder(p_str));
		/*
		SVScannerInput in = new SVScannerInput("param_processor", 
				new StringInputStream(p_str), 
				null, fObserver, fDefineProvider);
		 */
		int    ch = 0;
		String id;
		
		ch = in.skipWhite(in.get_ch());
		if (ch != '(') {
			in.unget_ch(ch);
		}

		while (ch != -1) {
			SVClassIfcModParam p;
			ch = in.skipWhite(in.get_ch());

			id = in.readIdentifier(ch);

			if (id == null) {
				break;
			}

			if (id.equals("type")) {
				ch = in.skipWhite(in.get_ch());
				id = in.readIdentifier(ch);
			}

			// id now holds the template identifier
			p = new SVClassIfcModParam(id);

			ch = in.skipWhite(in.get_ch());

			if (ch == '(') {
				ch = in.skipPastMatch("()");
			}

			ch = in.skipWhite(ch);
			
			if (ch == '=') {
				ch = in.skipWhite(in.get_ch());
				if ((id = in.readIdentifier(ch)) != null) {
					p.setDefault(id);
				}
			}

			while (ch != -1 && ch != ',') {
				ch = in.get_ch();
			}
			
			ret.add(p);
		}
		
		return ret;
	}
	
	private void process_import(String type) throws SVParseException {
		int ch = skipWhite(get_ch());
		
		if (ch == '"') {
			// likely  DPI import/export. Double-check
			String qualifier = readString(ch);
			
			if (qualifier != null && qualifier.equals("DPI") || qualifier.equals("DPI-C")) {
				String id;
				int modifiers = ISVScannerObserver.FieldAttr_DPI;
				ch = skipWhite(get_ch());
				
				if ((id = readIdentifier(ch)) != null) {
					Pair<String, Integer> qual_ret = scan_qualifiers(id, false);
					ch = skipWhite(get_ch());
				
					id        = qual_ret.fField1;
					modifiers |= qual_ret.fField2;
				
					// Read tf extern declaration
					if (id != null) {
						process_task_function(modifiers, id);
					}
				}
			}
		} else if (type.equals("import")) {
			// skip to end-of-statement
			startCapture(ch);
			while ((ch = get_ch()) != -1 && 
					!Character.isWhitespace(ch) && ch != ';') {
			}
			String imp_str = endCapture();

			import_statment(imp_str);

			if (ch == ';') {
				unget_ch(ch);
			}
		}
	}
	
	private void process_export(String type) throws EOFException {
		int ch = skipWhite(get_ch());

		String qualifier = readString(ch);
		
		if (qualifier != null && qualifier.equals("DPI") || qualifier.equals("DPI-C")) {
			ch = skipWhite(get_ch());
			
			String kind = readIdentifier(ch);
			
			ch = skipWhite(get_ch());
			
			String id = readIdentifier(ch);
			
			if (kind != null && id != null) {
				
			}
			
			System.out.println("EXPORT \"" + kind + "\" \"" + id + "\"");
		}
	}
	
	private void process_typedef() throws SVParseException {
		
		// typedef <type> <name>;
		
		int ch = skipWhite(get_ch());
		
		SVTypeInfo type = readTypeName(ch, false);
		
		ch = skipWhite(get_ch());
		
		if (SVCharacter.isSVIdentifierPart(ch)) {
			String id = readIdentifier(ch);
			
			if (type != null) {
				if (!type.fStructType) {
					typedef(id, type);
				} else {
					fStmtLocation = getLocation();
					leave_struct_decl(id);
				}
			}
		}
	}
	
	static private final Map<String, Integer>	fFieldQualifers;
	static private final Map<String, Integer>	fTaskFuncParamQualifiers;
	static {
		fFieldQualifers = new HashMap<String, Integer>();
		fFieldQualifers.put("local", ISVScannerObserver.FieldAttr_Local);
		fFieldQualifers.put("static", ISVScannerObserver.FieldAttr_Static);
		fFieldQualifers.put("protected", ISVScannerObserver.FieldAttr_Protected);
		fFieldQualifers.put("virtual", ISVScannerObserver.FieldAttr_Virtual);
		fFieldQualifers.put("automatic", ISVScannerObserver.FieldAttr_Automatic);
		fFieldQualifers.put("rand", ISVScannerObserver.FieldAttr_Rand);
		fFieldQualifers.put("randc", ISVScannerObserver.FieldAttr_Randc);
		fFieldQualifers.put("extern", ISVScannerObserver.FieldAttr_Extern);
		fFieldQualifers.put("const", ISVScannerObserver.FieldAttr_Const);
		fFieldQualifers.put("pure", ISVScannerObserver.FieldAttr_Pure);
		fFieldQualifers.put("context", ISVScannerObserver.FieldAttr_Context);
		fFieldQualifers.put("__sv_builtin_global", ISVScannerObserver.FieldAttr_SvBuiltinGlobal);
		
		fTaskFuncParamQualifiers = new HashMap<String, Integer>();
		fTaskFuncParamQualifiers.put("pure", 0); // TODO
		fTaskFuncParamQualifiers.put("virtual", ISVScannerObserver.ParamAttr_Virtual);
		fTaskFuncParamQualifiers.put("input", ISVScannerObserver.ParamAttr_Input);
		fTaskFuncParamQualifiers.put("output", ISVScannerObserver.ParamAttr_Output);
		fTaskFuncParamQualifiers.put("inout", ISVScannerObserver.ParamAttr_Inout);
		fTaskFuncParamQualifiers.put("ref", ISVScannerObserver.ParamAttr_Ref);
	}
	
	private boolean isFieldQualifier(String id) {
		return fFieldQualifers.containsKey(id);
	}
	
	private boolean isTaskFuncParamQualifier(String id) {
		return fTaskFuncParamQualifiers.containsKey(id);
	}
	
	
	private static SVDBItem			fSpecialNonNull = new SVDBItem("SPECIAL_NON_NULL", SVDBItemType.VarDecl);
	
	public SVDBItem process_module_class_interface_body_item(
			String	scope,
			String 	id) throws SVParseException {
		int     ch=-1, modifiers = 0;
		SVDBItem ret = null;
		
		debug("--> process_module_class_interface_body_item: \"" + id + "\"");
		
		// Ignore modifiers for now
		lexer().next_token(); // ch = skipWhite(get_ch());
		
		// unget_ch(ch);
		Pair<String, Integer> qual_ret = scan_qualifiers(id, false);
		// ch = skipWhite(get_ch());
		
		id        = qual_ret.fField1;
		modifiers = qual_ret.fField2;
		
		if (id == null) {
			System.out.println("[ERROR] id=null @ " + 
					getStmtLocation().getFileName() + ":" + 
					getStmtLocation().getLineNo());
			return ret;
		}
		
		debug("body item is: " + id);
		
		if (id.equals("task") || id.equals("function")) {
			// unget_ch(ch);
			ret = process_task_function(modifiers, id);
		} else if (id.equals("property")) {
			// unget_ch(ch);
			ret = process_property(id);
		} else if (id.equals("always") || id.equals("initial")) {
			// unget_ch(ch);
			process_initial_always(id);
			ret = fSpecialNonNull;
		} else if (id.equals("assign")) {
			// unget_ch(ch);
			process_assign();
			ret = fSpecialNonNull;
		} else if (id.equals("constraint")) {
			// unget_ch(ch);
			process_constraint(id);
			ret = fSpecialNonNull;
		} else if (id.equals("covergroup")) {
			// unget_ch(ch);
			process_covergroup(id);
			ret = fSpecialNonNull;
		} else if (id.equals("sequence")) {
			// unget_ch(ch);
			process_sequence(id);
			ret = fSpecialNonNull;
		} else if (id.equals("import")) {
			// unget_ch(ch);
			process_import(id);
			ret = fSpecialNonNull;
		} else if (id.startsWith("end") && SVKeywords.isSVKeyword(id)) {
			// it's likely that we've encountered a parse error 
			// or incomplete text section.
			if (fSemanticScopeStack.size() > 0) {
				// We've hit end of our current section
				if (("end" + fSemanticScopeStack.peek()).equals(id)) {
					fSemanticScopeStack.pop();
				}
			}
		} else if (id.equals("typedef")) {
			// unget_ch(ch);
			process_typedef();
			ret = fSpecialNonNull;
		} else if (id.equals("class") && scope.equals("module")) {
			// unget_ch(ch);
			ret = process_interface_module_class(id);
			fNewStatement = true;
		} else if (isFirstLevelScope(id, modifiers)) {
			// We've hit a first-level qualifier. This probably means that
			// there is a missing
			unget_str(id + " ");
			fNewStatement = true;
			ret = null; 
		} else if (ch == ':') {
			// Labeled statement -- often a cover
			System.out.println("labeled statement: " + id);
			System.out.println("    " + getLocation().getFileName() + ":" + getLocation().getLineNo());
			fNewStatement = true;
			ret = null; 
		} else {
			// likely a variable or module declaration
			
			debug("Likely VarDecl: " + id);
			
			unget_ch(ch);
			unget_str(id + " ");
			
			scanVariableDeclaration(modifiers);
			ret = fSpecialNonNull;
		}
		
		debug("<-- process_module_class_interface_body_item");
		
		return ret;
	}
	
	/**
	 * scanVariableDeclaration()
	 * 
	 * Scans through a list of variable declarations
	 * 
	 * Expects first string(s) read to be the type name
	 */
	private boolean scanVariableDeclaration(int modifiers) throws SVParseException {
		List<SvVarInfo> 	vars = new ArrayList<SvVarInfo>();
		SVTypeInfo			type;
		int 				ch;
		boolean         	is_variable = true;
		
		ch = skipWhite(get_ch());
		
		type = readTypeName(ch, false);
		ch = skipWhite(get_ch());

		// bail out if there's an error
		if (type == null || type.fTypeName == null ||
				type.fTypeName.equals("begin") || 
				type.fTypeName.equals("end")) {
			return false;
		}

		// First, skip qualifiers
		/*
		if (ch == '#') {
			ch = skipWhite(get_ch());
			
			if (ch == '(') {
				ch = skipPastMatch("()");
				ch = skipWhite(ch);
			}
		}
		
		if (ch == '[') {
			ch = skipPastMatch("[]");
			ch = skipWhite(ch);
		}
		 */
		
		// Handle parameterization
		do {
			
			if (ch == ',') {
				ch = get_ch();
			}
			
			ch = skipWhite(ch);
		
			String inst_name_or_var = readIdentifier(ch);
			
			if (inst_name_or_var == null) {
				is_variable = false;
				break;
			}
			
			debug("inst name or var: " + inst_name_or_var);
			
			ch = skipWhite(get_ch());
			
			SvVarInfo var_info = new SvVarInfo();
			var_info.fName = inst_name_or_var;
			vars.add(var_info);
			
			if (ch == '(') {
				type.fModIfc = true;
				
				// it's a module
				debug("module instantation - " + inst_name_or_var);
				ch = skipPastMatch("()");
				
				if (ch == ';') {
					unget_ch(ch);
				}
				break;
			} else if (ch == '[') {
				// Array type
				startCapture();
				skipPastMatch("[]");
				String bounds = endCapture();
				
				bounds = bounds.substring(0, bounds.length()-1).trim();
				
				if (bounds != null) {
					// remove ']'
					bounds = bounds.substring(0, bounds.length()-1);
					bounds = bounds.trim();
					
					if (bounds.startsWith("$")) {
						var_info.fAttr |= SvVarInfo.Attr_Queue;
					} else if (bounds.equals("")) {
						var_info.fAttr |= SvVarInfo.Attr_DynamicArray;
					} else {
						// TODO: Don't really know. Could be a fixed-size array or
						// a fixed-size array
						if (bounds.equals("*")) {
							var_info.fAttr |= SvVarInfo.Attr_AssocArray;
						} else {
							var_info.fArrayDim = bounds;
						}
					}
				}
			}

			ch = skipWhite(ch);
		} while (ch == ',');
		
		if (ch != -1) {
			unget_ch(ch);
		}
		
		if (vars.size() > 0) {
			variable_decl(type, modifiers, vars);
		}
		
		return is_variable;
	}
			
	
	public static boolean isFirstLevelScope(String id, int modifiers) {
		return (id.equals("class") ||
				// virtual interface is a valid field
				(id.equals("interface") && (modifiers & ISVScannerObserver.FieldAttr_Virtual) == 0) ||
				id.equals("struct") ||
				id.equals("module"));
	}
	
	public static boolean isSecondLevelScope(String id) {
		return (id.equals("task") ||
				id.equals("function") ||
				id.equals("always") ||
				id.equals("initial"));
	}
	
	/**
	 * scan_statement()
	 */
	public String scan_statement() {
		int     ch;
		
		while ((ch = get_ch()) != -1) {
			switch (ch) {
				case ';':
				case '\n':
					// Typically mark the end of statements
					fNewStatement = true;
					break;

				// Ignore whitespace...
				case ' ':
				case '\t':
					break;
					
				default:
					if (fNewStatement) {
						fStmtLocation = getLocation();
						if (SVCharacter.isSVIdentifierStart(ch)) {
							unget_ch(ch);
							fLexer.next_token();
							if (fLexer.isIdentifier()) {
								fNewStatement = false;
							}
							return fLexer.getImage();
						} else if (ch == '`') {
							System.out.println("[ERROR] pre-processor directive encountered");
							/*
							ch = skipWhite(get_ch());
							handle_preproc_directive(readIdentifier(ch));
							 */
							
							fNewStatement = true;
						}
					}
					break;
			}
		}
		
		return null;
	}

	/**
	 * Read an identifier from the input stream
	 * 
	 * @param ci
	 * @return
	 */
	private String readIdentifier(int ci) throws EOFException {
		return fInput.readIdentifier(ci);
	}
	
	private String readString(int ci) {
		return fInput.readString(ci);
	}
	
	/* Currently unused
	private String readLine(int ci) throws EOFException {
		if (fInputStack.size() > 0) {
			return fInputStack.peek().readLine(ci);
		} else {
			return "";
		}
	}
	 */

	private String readQualifiedIdentifier(int ci) throws EOFException {
		if (!SVCharacter.isSVIdentifierStart(ci)) {
			unget_ch(ci);
			return null;
		}
		StringBuffer ret = new StringBuffer();
		
		ret.append((char)ci);
		
		while ((ci = get_ch()) != -1 && 
				(SVCharacter.isSVIdentifierPart(ci) || ci == ':')) {
			ret.append((char)ci);
		}
		unget_ch(ci);
		
		return ret.toString();
	}
	
	private String readExpression(int ci) throws EOFException {
		StringBuilder ret = new StringBuilder();
		
		while (true) {
			if (ci == '(') {
				startCapture(ci);
				unget_ch(skipPastMatch("()"));
				ret.append(endCapture());
			} else if (SVCharacter.isSVIdentifierStart(ci)) {
				ret.append(readIdentifier(ci));
			} else {
				break;
			}
			
			ci = skipWhite(get_ch());
			
			if (ci == '.') {
				ret.append((char)ci);
			} else if (ci == ':' && (ci = get_ch()) == ':') {
				ret.append("::");
			} else {
				break;
			}
			
			ci = skipWhite(get_ch());
		}
		
		return ret.toString();
	}

	private boolean isBuiltInType(String id) {
		return (id.equals("int") || id.equals("integer") || 
				id.equals("unsigned") || id.equals("signed") ||
				id.equals("bit") || id.equals("void") ||
				id.equals("longint") || id.equals("chandle") ||
				id.equals("real") || id.equals("shortreal"));
	}
	
	private SVTypeInfo readTypeName(int ch, boolean task_func) throws SVParseException {
		StringBuffer ret = new StringBuffer();
		String id = null;
		SVTypeInfo type = new SVTypeInfo();
		int    is_builtin = 0;
		int    is_qual    = 0;
		int    idx        = 0;
		
		debug("--> readTypeName(task_func=" + task_func + ") - ch=" + (char)ch);
		while (true) {
			debug("    ch=" + (char)ch);
			ch = skipWhite(ch);

			debug("    pre-readQualifiedIdentifier ch=" + (char)ch);
			
			while (ch == '[') {
				String bitrange;
				startCapture(ch);
				ch = skipPastMatch("[]", "[");
				bitrange = endCapture();
				
				// Ensure the last character is removed. 
				bitrange = bitrange.substring(0, bitrange.length()-1).trim();
				
				ret.append(" ");
				ret.append(bitrange);
				ret.append(" ");
				is_builtin |= (1 << idx);
				ch = skipWhite(ch);
				
				type.fVectorDim = bitrange;
			}
			
			if (!SVCharacter.isSVIdentifierStart(ch)) {
				break;
			}
			
			id = readQualifiedIdentifier(ch);
			ch = -1;

			debug("    id=" + id);
			
			if (isBuiltInType(id)) {
				is_builtin |= (1 << idx);
			} else {
				if ((task_func && isTaskFuncParamQualifier(id)) ||
						(!task_func && isFieldQualifier(id))) {
					is_qual |= (1 << idx);
				}
			}

			if ((is_builtin & (1 << idx)) != 0) {
				ret.append(" ");
				ret.append(id);
			} else if ((is_qual & (1 << idx)) == 0) {
				if (idx == 0 || 
						(is_builtin == 0 && (is_qual & (1 << (idx-1))) != 0)) {
					// assume this is a user-defined type
					ret.append(id);
					
					ch = skipWhite(get_ch());
					// Allow parameterized types
					if (ch == '#') {
						ch = skipWhite(get_ch());
						
						if (ch == '(') {
							startCapture(ch) ;
							ch = skipPastMatch("()");
							String templ = endCapture();
							
							type.fParameters = parse_parameter_str(templ);
						}
					}
					unget_ch(ch);
				} else {
					unget_str(" " + id);
					break;
				}
			}
			
			ch = skipWhite(get_ch());
			
			while (ch == '[') {
				String bitrange;
				startCapture(ch);
				ch = skipPastMatch("[]", "[");
				bitrange = endCapture();
				
				// Ensure the last character is removed. 
				bitrange = bitrange.substring(0, bitrange.length()-1).trim();
				
				
				ret.append(" ");
				ret.append(bitrange);
				ret.append(" ");
				ch = skipWhite(ch);
				type.fVectorDim = bitrange;
			}
			
			idx++;
		}
		
		if (ch != -1) {
			unget_ch(ch);
		}
		
		debug("<-- readTypeName(task_func=" + task_func + ") -> " + 
				ret.toString().trim());
		if (ret.length() != 0) {
			String type_name = ret.toString().trim();
			
			if (type_name.startsWith("enum")) {
				// Could be enum <basetype>
				
				ch = skipWhite(get_ch());
				
				type.fEnumType = true;
				type.fEnumVals = new ArrayList<SVEnumVal>();
				
				if (ch == '{') {
					long c_val = 0;
					
					// we're probably scanning a typedef
					do {
						ch = skipWhite(get_ch());
						
						id = readIdentifier(ch);
						long val_i = -1;
						
						ch = skipWhite(get_ch());
						
						if (ch == '=') {
							ch = skipWhite(get_ch());
							
							startCapture(ch);
							
							// handle optional equals clause
							while ((ch = get_ch()) != -1 &&
									ch != ',' && ch != '}') {
								// skip to the next item
							}
							
							String val = endCapture();
							
							if (val.endsWith(",") || val.endsWith("}")) {
								val = val.substring(0, val.length()-1);
							}
							val = val.trim();
							
							
							try {
								val_i = VerilogNumberParser.parseLong(val);
								c_val = val_i;
							} catch (NumberFormatException e) {
								System.out.println("[WARN] problem parsing enum val \"" + 
										val + "\"");
							}
						}

						type.fEnumVals.add(new SVEnumVal(id, c_val));
						c_val++;

						if (ch != ',') {
							break;
						}
					} while (true);
				} else {
					// likely we're scanning an in-line declaration
				}
			} else if (type_name.startsWith("struct")) {
				type.fStructType = true;
				type.fTypeName   = type_name;
				process_struct_decl(type);
			} else if (type_name.startsWith("class")) {
				type.fClassType = true;
				type.fTypeName  = type_name;
			} else {
				type.fTypeName = type_name;
			}
			
			if (type.fTypeName != null || type.fEnumType) {
				return type;
			} else {
				System.out.println("TypeName == null");
				return null;
			}
		} else {
			System.out.println("ret.length == 0");
			return null;
		}
	}
	
	private int skipWhite(int ch) throws EOFException {
		return fInput.skipWhite(ch);
	}

	private void startCapture(int ch) {
		fInput.startCapture(ch);
	}

	private void startCapture() {
		startCapture(-1);
	}
	
	private String endCapture() throws EOFException {
		return fInput.endCapture();
	}

	private int skipPastMatch(String pair) throws EOFException {
		return fInput.skipPastMatch(pair);
	}

	private int skipPastMatch(String pair, String escape) throws EOFException {
		return fInput.skipPastMatch(pair, escape);
	}

	private int get_ch() {
		return get_ch(true);
	}
	
	private void unget_str(String str) {
		fInput.unget_str(str);
	}
	
	/*
	 * low-level character-retrieval. 
	 */
	private int get_ch(boolean eof_ex) throws EOFException {
		int ch = -1;

		ch = fInput.get_ch();
		
		if (eof_ex && ch == -1) {
			throw new EOFException();
		}
		
		return ch;
	}
	
	private void unget_ch(int ch) {
		fInput.unget_ch(ch);
	}
	
	public ScanLocation getLocation() {
		return fInput.getLocation();
	}

	private void debug(String msg) {
		System.out.println(msg);
	}

	public void error(String msg, String filename, int lineno) {
		SVDBMarkerItem marker = new SVDBMarkerItem(
				SVDBMarkerItem.MARKER_ERR,
				SVDBMarkerItem.KIND_GENERIC, msg);
		marker.setLocation(new SVDBLocation(fFile, lineno, 0));
		
		fFile.addItem(marker);
	}
	
	public SVDBFile parse(InputStream in, String name) {
		fScopeStack.clear();
		
		fFile = new SVDBFile(name);
		fScopeStack.push(fFile);
		scan(in, name);
		
		return fFile;
	}
	
	public void init(InputStream in, String name) {
		fScopeStack.clear();
		fFile = new SVDBFile(name);
		fScopeStack.push(fFile);
		
		fNewStatement = true;
		
		if (fDefineProvider != null) {
			fDefineProvider.addErrorListener(this);
		}
		
		SVPreProcScanner pp = new SVPreProcScanner();
		pp.setDefineProvider(fDefineProvider);
		pp.setScanner(this);
		pp.setObserver(this);
		
		pp.init(in, name);
		pp.setExpandMacros(true);
		pp.setEvalConditionals(fEvalConditionals);
		
		fInput = new SVScannerTextScanner(pp);
		fLexer = new SVLexer();
		fLexer.init(this);
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

	
	public void leave_interface_decl() {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Interface) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	
	public void leave_class_decl() throws HaltScanException {
		if (fScopeStack.size() > 0 && 
				fScopeStack.peek().getType() == SVDBItemType.Class) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void leave_struct_decl(String name) throws HaltScanException {
		if (fScopeStack.size() > 0 &&
				fScopeStack.peek().getType() == SVDBItemType.Struct) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop().setName(name);
		}
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

	private void setStartLocation(SVDBItem item) {
		ScanLocation loc = getStartLocation();
		
		if (loc != null) {
			item.setLocation(new SVDBLocation(fFile, loc.getLineNo(), loc.getLinePos()));
		}
	}
	
	private void setLocation(SVDBItem item) {
		ScanLocation loc = getStmtLocation();
		item.setLocation(new SVDBLocation(fFile, loc.getLineNo(), loc.getLinePos()));
	}
	
	private void setEndLocation(SVDBScopeItem item) {
		ScanLocation loc = getStmtLocation();
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
	
	public void enter_preproc_conditional(String type, String conditional) {
		
	}

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

	public boolean error_limit_reached() {
		// TODO Auto-generated method stub
		return false;
	}

	public SVLexer lexer() {
		return fLexer;
	}

	public ITextScanner scanner() {
		return fInput;
	}

	public void warning(String msg, int lineno) {
		System.out.println("[FIXME] warning \"" + msg + "\" @ " + lineno);
	}
	
	public void error(String msg, int lineno) {
		System.out.println("[FIXME] error \"" + msg + "\" @ " + lineno);
	}

	public SVParsers parsers() {
		return fSVParsers;
	}
	
	
	
}
