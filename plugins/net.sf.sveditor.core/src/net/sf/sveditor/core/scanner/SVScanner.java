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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

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
public class SVScanner implements ISVScanner, IPreProcErrorListener {
	private Stack<String>			fScopeStack = new Stack<String>();
	private SVScannerTextScanner		fInput;
	
	private boolean					fNewStatement;
	private ScanLocation			fStmtLocation;
	private ScanLocation			fStartLocation;
	
	private ISVScannerObserver		fObserver;
	private IDefineProvider			fDefineProvider;
	private boolean					fEvalConditionals = true;
	
	public SVScanner() {
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
	
	public void setObserver(ISVScannerObserver observer) {
		fObserver = observer;
	}
	
	public void preProcError(String msg, String filename, int lineno) {
		if (fObserver != null) {
			fObserver.error(msg, filename, lineno);
		}
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
		pp.setObserver(fObserver);
		
		pp.init(in, filename);
		pp.setExpandMacros(true);
		pp.setEvalConditionals(fEvalConditionals);
		
		fInput = new SVScannerTextScanner(pp);
		
		if (fObserver != null) {
			fObserver.enter_file(filename);
		}

		process();

		if (fObserver != null) {
			fObserver.leave_file();
		}
		
		if (fDefineProvider != null) {
			fDefineProvider.removeErrorListener(this);
		}
	}
	
	private void process() {
		String id;
		
		try {
			while ((id = scan_statement()) != null) {
				Pair<String, Integer> ret = scan_qualifiers(id, false);
				id = ret.fField1;

				if (id != null) {
					if (id.equals("module") ||
							id.equals("interface") ||
							id.equals("class") || id.equals("program")) {
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
				ch = skipWhite(next_ch());
				
				if (ch == '(') {
					ch = skipPastMatch("()");
				}
				expr = endCapture();
			} else if (ch == '#') {
				startCapture(ch);
				ch = skipWhite(next_ch());
				
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
		
		if (fObserver != null) {
			fObserver.enter_initial_always_block(type, expr);
		}
		
		if (id != null && id.equals("begin")) {
			int begin_cnt = 1;
			int end_cnt = 0;

			ch = skipWhite(next_ch());
			
			if (ch == ':') {
				// named begin
				ch = skipWhite(next_ch());
				
				if (Character.isJavaIdentifierStart(ch)) {
					name = readIdentifier(ch);
				}
			} else {
				unget_ch(ch);
			}
			
			do {
				do {
					ch = skipWhite(next_ch());
				} while (ch != -1 && !Character.isJavaIdentifierStart(ch));
				
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
		
		if (fObserver != null) {
			fObserver.leave_initial_always_block(name);
		}
	}
	
	private void process_assign() throws EOFException {
		int ch = skipWhite(get_ch());
		String target = "";

		if (ch == '(' || Character.isJavaIdentifierStart(ch)) {
			target = readExpression(ch);
		} else if (ch == '{') {
			startCapture(ch);
			ch = skipPastMatch("{}");
			target = endCapture();
		}
		
		if (fObserver != null) {
			fObserver.assign_stmt(target);
		}
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
			
			if (fObserver != null) {
				fObserver.constraint(cname, expr);
			}
		}
		
		fNewStatement = true;
	}
	
	private void process_covergroup(String id) throws EOFException {
		int ch = get_ch();
		
		
		fScopeStack.push("covergroup");
		
		
		ch = skipWhite(ch);
		
		String cg_name = readIdentifier(ch);

		if (fObserver != null) {
			fObserver.enter_covergroup(cg_name);
		}

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
					ch = skipWhite(next_ch());
					String name = id;
					
					String type = readIdentifier(ch);
					
					// Now, skip forward and try to read the target
					ch = skipWhite(get_ch());
					
					// read any expression character
					startCapture(ch);
					while (ch != -1 && ch != '{' && ch != ';') {
						ch = next_ch();
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
					if (fObserver != null) {
						fObserver.covergroup_item(name, type, target, body);
					}
					fNewStatement = true;
				}
			}
		}
		
		handle_leave_scope();
	}
	
	private void process_sequence(String id) throws EOFException {
		
		int ch = skipWhite(get_ch());
		
		String name = readIdentifier(ch);
		fScopeStack.push("sequence");
		
		if (fObserver != null) {
			fObserver.enter_sequence(name);
		}
		
		while ((id = scan_statement()) != null) {
			if (id.equals("endsequence")) {
				break;
			}
		}
		
		handle_leave_scope();
	}
	
	private void process_property(String id) throws EOFException {
		int ch = skipWhite(get_ch());
		
		String name = readIdentifier(ch);
		fScopeStack.push("property");
		
		if (fObserver != null) {
			fObserver.enter_property(name);
		}
		
		while ((id = scan_statement()) != null) {
			if (id.equals("endproperty")) {
				break;
			}
		}
		
		handle_leave_scope();
	}
	
	private class Pair <T1, T2> {
		T1			fField1;
		T2			fField2;
	}
	
	private Pair<String, Integer> scan_qualifiers(String id, boolean param) throws EOFException {
		Pair<String, Integer> ret = new Pair<String, Integer>();
		int modifiers = 0;
		int ch = get_ch();
		Map<String, Integer>	qmap = (param)?fTaskFuncParamQualifiers:fFieldQualifers;
		
		ret.fField2 = 0;
		while (qmap.containsKey(id)) {
			debug("item modified by \"" + id + "\"");
			modifiers |= qmap.get(id);
			
			ch = skipWhite(ch);
			id = readIdentifier(ch);
			ch = skipWhite(get_ch());
		}
		
		unget_ch(ch);
		
		ret.fField1 = id;
		ret.fField2 = modifiers;
		
		return ret;
	}
	
	private boolean process_task_function(int modifiers, String id) throws EOFException {
		// Scan for end-of-section
		String 						tf_name;
		String						ret_type = null;
		List<SVTaskFuncParam>		params = new ArrayList<SVTaskFuncParam>();
		boolean ret = true;
		int ch = skipWhite(get_ch());
		
		fScopeStack.push(id);
		
		tf_name = readIdentifier(ch);
		ch = skipWhite(get_ch());

		unget_ch(ch);
		Pair<String, Integer> mod_ret = scan_qualifiers(tf_name, false);
		ch = get_ch();

		tf_name   = mod_ret.fField1;
		modifiers |= mod_ret.fField2;

		
		if (id.equals("function")) {
			// could have a return type.
			unget_ch(ch);
			unget_str(tf_name + " ");
			ch = skipWhite(next_ch());
			SVTypeInfo typename = readTypeName(ch, false);
			ret_type = typename.fTypeName;
			ch = skipWhite(next_ch());
			
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
				ch = skipWhite(next_ch());
				cnt++;
			}
			
			debug("next_ch=" + (char)ch);
			
			do {
				ch = skipWhite(ch);

				if (ch == ';' || ch == ')') {
					break;
				}

				t = readTypeName(ch, true);
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
					
					t.fTypeName += capture; 
					ch = skipWhite(ch);
				}
				
				SVTaskFuncParam p = new SVTaskFuncParam(t.fTypeName, n);
				params.add(p);
				
				ch = skipWhite(ch);

				if (ch == '=') {
					ch = skipWhite(next_ch());
					while (ch != -1 && ch != ',' && ch != ')' &&
							!Character.isWhitespace(ch)) {
						ch = next_ch();
					}
					ch = skipWhite(ch);
				}
				
				if (ch == ';' || ch == ')') {
					break;
				}
				
				ch = skipWhite(ch);
				if (ch == ',') {
					ch = skipWhite(next_ch());
				} else {
					break;
				}
			} while (t != null && ch != ')' && ch != -1);
		}
		
		if (fObserver != null) {
			if (ret_type != null) {
				fObserver.enter_func_decl(tf_name, modifiers, ret_type, params);
			} else {
				fObserver.enter_task_decl(tf_name, modifiers, params);
			}
		}
		
		debug("" + id + " " + tf_name);
		
		boolean has_body = true;
		
		if ((modifiers & ISVScannerObserver.FieldAttr_Extern) != 0 ||
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
			boolean var_enabled = true;
			
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
//					System.out.println("id \"" + id + "\" is a second-level scope");
					if (fObserver != null) {
						fObserver.error("missing \"" + exp_end + "\"",
								getLocation().getFileName(),
								getLocation().getLineNo());
						System.out.println("second-level scope \"" + id + "\"");
					}

					// 
					fNewStatement = true;
					unget_str(id + " ");
					break;
				} else if (isFirstLevelScope(id, 0)) {
//					System.out.println("id \"" + id + "\" is a first-level scope");
					if (fObserver != null) {
						fObserver.error("missing \"" + exp_end + "\"",
								getLocation().getFileName(),
								getLocation().getLineNo());
					}

					System.out.println("first-level scope \"" + id + "\" " + tf_name);

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
		} else {
			debug("    extern task/function declaration");
		}
		
		handle_leave_scope();
		
		return ret;
	}
	
	private void process_interface_module_class(String type) throws EOFException {
		String id;
		List<SVClassIfcModParam>	params = null;
		String super_name = null;
		List<SVClassIfcModParam>	super_params = null;
		String module_type_name = null;
		String ports = null;
		int ch = skipWhite(next_ch());
		
		debug("--> process_module()");

		fScopeStack.push(type);
		
		//
		// Skip up to point of module type name
		//
		
		ch = skipWhite(ch);
		
		if (Character.isJavaIdentifierStart(ch)) {
			module_type_name = readIdentifier(ch);
			ch = get_ch();
			debug("  module_type_name=" + module_type_name);
		} else {
			return;
		}

		// Handle modules with parameters
		ch = skipWhite(ch);
		if (ch == '#') {
			ch = skipWhite(next_ch());
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
			if (Character.isJavaIdentifierPart(ch)) {
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
							ch = skipWhite(next_ch());
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
		
		if (fObserver != null) {
			if (type.equals("module")) {
				fObserver.enter_module_decl(module_type_name, ports);
			} else if (type.equals("program")) {
				fObserver.enter_program_decl(module_type_name);
			} else if (type.equals("interface")) {
				fObserver.enter_interface_decl(module_type_name, ports);
			} else if (type.equals("class")) {
				fObserver.enter_class_decl(module_type_name, params, super_name, super_params);
			} else if (type.equals("struct")) {
				fObserver.enter_struct_decl(module_type_name, params);
			}
		}

		while ((id = scan_statement()) != null) {
			boolean ret;
			debug("id=" + id);
			if (id.equals("end" + type)) {
				break;
			}
			ret = process_module_class_interface_body_item(type, id);

			// Check whether we aborted parsing the body because
			// we found a 1st-level scope keyword
			if (!ret) {
				break;
			}
		}
		
		// Pop the first-level scope
		handle_leave_scope();
		
		debug("<-- process_module()");
	}
	
	private void process_struct_decl(SVTypeInfo type_info) throws EOFException {
		int ch = skipWhite(get_ch());
		
		System.out.println("process_struct_decl");
		
		while (Character.isJavaIdentifierStart(ch)) {
			/* String qual = */ readIdentifier(ch);
			
			ch = skipWhite(get_ch());
		}
		
		if (ch != '{') {
			return;
		}
		
		if (fObserver != null) {
			fObserver.enter_struct_decl("", null);
		}
		
		String id;
		
		while ((id = scan_statement()) != null) {
			boolean ret = process_module_class_interface_body_item("struct", id);
			
			if (!ret) {
				break;
			}
			

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
			if (fObserver != null) {
				fStmtLocation = getLocation();
				fObserver.leave_struct_decl("ANONYMOUS");
			}
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
			int ch = skipWhite(next_ch());
			String pkg = readQualifiedIdentifier(ch);
			fObserver.enter_package(pkg);
		} else {
			if (fObserver != null) {
				fObserver.leave_package();
			}
		}
	}
	
	private void handle_leave_scope() {
		handle_leave_scope(1);
	}
	
	private void handle_leave_scope(int levels) {
		fStmtLocation = getLocation();
		for (int i=0; i<levels; i++) {
			String type = null;
			
			if (fScopeStack.size() > 0) {
				type = fScopeStack.pop();
			} else {
				System.out.println("[ERROR] attempting to leave scope @ " + 
						getLocation().getFileName() + ":" +
						getLocation().getLineNo());
			}
			
			if (type != null && fObserver != null) {
				if (type.equals("module")) {
					fObserver.leave_module_decl();
				} else if (type.equals("program")) {
					fObserver.leave_program_decl();
				} else if (type.equals("interface")) {
					fObserver.leave_interface_decl();
				} else if (type.equals("class")) {
					fObserver.leave_class_decl();
				} else if (type.equals("struct")) {
					fObserver.leave_struct_decl("");
				} else if (type.equals("task")) {
					fObserver.leave_task_decl();
				} else if (type.equals("function")) {
					fObserver.leave_func_decl();
				} else if (type.equals("covergroup")) {
					fObserver.leave_covergroup();
				} else if (type.equals("sequence")) {
					fObserver.leave_sequence();
				} else if (type.equals("property")) {
					fObserver.leave_property();
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

			ret.add(new SVClassIfcModParam(id));

			ch = in.skipWhite(in.get_ch());

			if (ch == '(') {
				ch = in.skipPastMatch("()");
			}

			ch = in.skipWhite(ch);

			while (ch != -1 && ch != ',') {
				ch = in.get_ch();
			}
		}
		
		return ret;
	}
	
	private void process_import(String type) throws EOFException {
		int ch = skipWhite(next_ch());
		
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
			while ((ch = next_ch()) != -1 && 
					!Character.isWhitespace(ch) && ch != ';') {
			}
			String imp_str = endCapture();

			if (fObserver != null) {
				fObserver.import_statment(imp_str);
			}

			if (ch == ';') {
				unget_ch(ch);
			}
		}
	}
	
	private void process_export(String type) throws EOFException {
		int ch = skipWhite(next_ch());

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
	
	private void process_typedef() throws EOFException {
		
		// typedef <type> <name>;
		
		int ch = skipWhite(get_ch());
		
		SVTypeInfo type = readTypeName(ch, false);
		
		ch = skipWhite(get_ch());
		
		if (Character.isJavaIdentifierPart(ch)) {
			String id = readIdentifier(ch);
			
			if (type != null) {
				if (fObserver != null) {
					if (!type.fStructType) {
						fObserver.typedef(id, type);
					} else {
						fStmtLocation = getLocation();
						fObserver.leave_struct_decl(id);
					}
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
	
	private boolean process_module_class_interface_body_item(
			String	scope,
			String 	id) throws EOFException {
		int     ch, modifiers = 0;
		boolean ret = true;
		
		debug("--> process_module_class_interface_body_item: \"" + id + "\"");
		
		// Ignore modifiers for now
		ch = skipWhite(get_ch());
		
		unget_ch(ch);
		Pair<String, Integer> qual_ret = scan_qualifiers(id, false);
		ch = skipWhite(get_ch());
		
		id        = qual_ret.fField1;
		modifiers = qual_ret.fField2;
		
		if (id == null) {
			System.out.println("[ERROR] id=null @ " + 
					getStmtLocation().getFileName() + ":" + 
					getStmtLocation().getLineNo());
			return false;
		}
		
		debug("body item is: " + id);
		
		if (id.equals("task") || id.equals("function")) {
			unget_ch(ch);
			ret = process_task_function(modifiers, id);
		} else if (id.equals("property")) {
			unget_ch(ch);
			process_property(id);
		} else if (id.equals("always") || id.equals("initial")) {
			unget_ch(ch);
			process_initial_always(id);
		} else if (id.equals("assign")) {
			unget_ch(ch);
			process_assign();
		} else if (id.equals("constraint")) {
			unget_ch(ch);
			process_constraint(id);
		} else if (id.equals("covergroup")) {
			unget_ch(ch);
			process_covergroup(id);
		} else if (id.equals("sequence")) {
			unget_ch(ch);
			process_sequence(id);
		} else if (id.equals("import")) {
			unget_ch(ch);
			process_import(id);
		} else if (id.startsWith("end") && SVKeywords.isSVKeyword(id)) {
			// it's likely that we've encountered a parse error 
			// or incomplete text section.
			if (fScopeStack.size() > 0) {
				// We've hit end of our current section
				if (("end" + fScopeStack.peek()).equals(id)) {
					fScopeStack.pop();
				}
			}
		} else if (id.equals("typedef")) {
			unget_ch(ch);
			process_typedef();
		} else if (id.equals("class") && scope.equals("module")) {
			unget_ch(ch);
			process_interface_module_class(id);
			fNewStatement = true;
		} else if (isFirstLevelScope(id, modifiers)) {
			// We've hit a first-level qualifier. This probably means that
			// there is a missing
			unget_str(id + " ");
			fNewStatement = true;
			ret = false; 
		} else if (ch == ':') {
			// Labeled statement -- often a cover
			System.out.println("labeled statement: " + id);
			System.out.println("    " + getLocation().getFileName() + ":" + getLocation().getLineNo());
			fNewStatement = true;
			ret = false; 
		} else {
			// likely a variable or module declaration
			
			debug("Likely VarDecl: " + id);
			
			unget_ch(ch);
			unget_str(id + " ");
			
			scanVariableDeclaration(modifiers);
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
	private boolean scanVariableDeclaration(int modifiers) throws EOFException {
		List<SvVarInfo> 	vars = new ArrayList<SvVarInfo>();
		SVTypeInfo			type;
		int 				ch;
		boolean         	is_variable = true;
		
		ch = skipWhite(next_ch());
		
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
			ch = skipWhite(next_ch());
			
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
				ch = next_ch();
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
		
		if (fObserver != null && vars.size() > 0) {
			fObserver.variable_decl(type, modifiers, vars);
		}
		
		return is_variable;
	}
			
	
	private boolean isFirstLevelScope(String id, int modifiers) {
		return (id.equals("class") ||
				// virtual interface is a valid field
				(id.equals("interface") && (modifiers & ISVScannerObserver.FieldAttr_Virtual) == 0) ||
				id.equals("struct") ||
				id.equals("module"));
	}
	
	private boolean isSecondLevelScope(String id) {
		return (id.equals("task") ||
				id.equals("function") ||
				id.equals("always") ||
				id.equals("initial"));
	}
	
	/**
	 * scan_statement()
	 */
	private String scan_statement() throws EOFException {
		int     ch;
		while ((ch = next_ch()) != -1) {
			switch (ch) {
				case ';':
				case '\n':
					// Typically mark the end of statements
					fNewStatement = true;
					// System.out.println("new statement @ " + getLocation().getLineNo() + "(" + (char)ch + ")");
					break;
					
				// Ignore whitespace...
				case ' ':
				case '\t':
					break;
					
				default:
					if (fNewStatement) {
						fStmtLocation = getLocation();
						String id = null;
						if (Character.isJavaIdentifierStart(ch)) {
							id = readIdentifier(ch);
							
							if (id != null) {
								fNewStatement = false;
							}
							
							return id;
						} else if (ch == '`') {
							System.out.println("[ERROR] pre-processor directive encountered");
							/*
							ch = skipWhite(next_ch());
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
		if (!Character.isJavaIdentifierStart(ci)) {
			unget_ch(ci);
			return null;
		}
		StringBuffer ret = new StringBuffer();
		
		ret.append((char)ci);
		
		while ((ci = get_ch()) != -1 && 
				(Character.isJavaIdentifierPart(ci) || ci == ':')) {
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
			} else if (Character.isJavaIdentifierStart(ci)) {
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
	
	private SVTypeInfo readTypeName(int ch, boolean task_func) throws EOFException {
		StringBuffer ret = new StringBuffer();
		String id = null;
		SVTypeInfo type = new SVTypeInfo();
		int    is_builtin = 0;
		int    is_qual    = 0;
		int    idx        = 0;

		debug("--> readTypeName(task_func=" + task_func + ")");
		while (true) {
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
			
			if (!Character.isJavaIdentifierStart(ch)) {
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
					
					ch = skipWhite(next_ch());
					// Allow parameterized types
					if (ch == '#') {
						ch = skipWhite(next_ch());
						
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
		
		debug("--> readTypeName(task_func=" + task_func + ") -> " + 
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
							while ((ch = next_ch()) != -1 &&
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

	/**
	 * next_ch()
	 * 
	 * Returns the next character, after skipping any comments
	 * 
	 * @return
	 */
	private int next_ch() throws EOFException {
		// return fInput.next_ch();
		return fInput.get_ch();
	}

	private int get_ch() throws EOFException {
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
		// System.out.println(msg);
	}
	
}
