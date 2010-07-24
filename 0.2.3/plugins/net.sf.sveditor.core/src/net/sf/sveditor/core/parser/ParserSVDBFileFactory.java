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
import net.sf.sveditor.core.db.IFieldItemAttr;
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
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBParamPort;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.SVDBTypedef;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.HaltScanException;
import net.sf.sveditor.core.scanner.IDefineProvider;
import net.sf.sveditor.core.scanner.IPreProcErrorListener;
import net.sf.sveditor.core.scanner.ISVPreProcScannerObserver;
import net.sf.sveditor.core.scanner.ISVScanner;
import net.sf.sveditor.core.scanner.ISVScannerObserver;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanner.SVClassIfcModParam;
import net.sf.sveditor.core.scanner.SVKeywords;
import net.sf.sveditor.core.scanner.SVPreProcScanner;
import net.sf.sveditor.core.scanner.SVScannerTextScanner;
import net.sf.sveditor.core.scanner.SVTypeInfo;
import net.sf.sveditor.core.scanner.SvVarInfo;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;
import net.sf.sveditor.core.scanutils.StringTextScanner;

/**
 * Scanner for SystemVerilog files.
 * 
 * @author ballance
 * 
 *         - Handle structures - Handle enum types - Handle export/import,
 *         "DPI-C", context as function/task qualifiers - type is always <type>
 *         <qualifier>, so no need to handle complex ordering (eg unsigned int)
 *         - handle property as second-level scope - recognize 'import' - handle
 *         class declaration within module - Handle sequence as empty construct
 */
public class ParserSVDBFileFactory implements ISVScanner,
		IPreProcErrorListener, ISVDBFileFactory, ISVPreProcScannerObserver,
		ISVParser {
	private Stack<String> fSemanticScopeStack;
	private SVScannerTextScanner fInput;
	private SVLexer fLexer;

	private boolean fNewStatement;
	private ScanLocation fStmtLocation;
	private ScanLocation fStartLocation;

	private IDefineProvider fDefineProvider;
	private boolean fEvalConditionals = true;

	private SVDBFile fFile;
	private Stack<SVDBScopeItem> fScopeStack;
	private SVParsers fSVParsers;
	private List<SVParseException> 		fParseErrors;
	private int							fParseErrorMax;
	private LogHandle					fLog;

	public ParserSVDBFileFactory(IDefineProvider dp) {
		setDefineProvider(dp);
		fScopeStack = new Stack<SVDBScopeItem>();
		fSemanticScopeStack = new Stack<String>();
		fSVParsers = new SVParsers(this);

		if (dp != null) {
			setDefineProvider(dp);
		}
		
		fParseErrors = new ArrayList<SVParseException>();
		fParseErrorMax = 5;
		fLog = LogFactory.getLogHandle("ParserSVDBFileFactory");
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
		fLexer.init(this, fInput);

		try {
			process_file();
		} catch (SVParseException e) {
			System.out.println("ParseException: post-process()");
			e.printStackTrace();
		} catch (EOFException e) {
			e.printStackTrace();
		}

		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.File) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}

		if (fDefineProvider != null) {
			fDefineProvider.removeErrorListener(this);
		}
	}

	private void process_file() throws SVParseException {
		String id;

		try {
			while ((id = scan_statement()) != null) {
				SVDBLocation start = lexer().getStartLocation();
				int modifiers = scan_qualifiers(false);
				id = lexer().peek();

				if (id != null) {
					if (id.equals("class")) {
						SVDBModIfcClassDecl cls = null;
						try {
							cls = parsers().classParser().parse(modifiers);
						} catch (SVParseException e) {
							System.out.println("ParseException: post-class()");
							e.printStackTrace();
						}
						fNewStatement = true;
					} else if (id.equals("module") || id.equals("macromodule") ||
							id.equals("interface") || id.equals("program")) {
						// enter module scope
						// TODO: should probably add this item to the 
						// File scope here
						try {
							parsers().modIfcProgParser().parse(modifiers);
						} catch (SVParseException e) {
							
						}
					} else if (id.equals("struct")) {
						process_struct_decl(null);
					} else if (id.equals("package") || id.equals("endpackage")) {
						process_package(id);
					} else if (id.equals("import")) {
						process_import();
						fNewStatement = true;
					} else if (id.equals("export")) {
						process_export(id);
					} else if (id.equals("typedef")) {
						for (SVDBTypedef td : process_typedef(false)) {
							if (fScopeStack.size() > 0) {
								fScopeStack.peek().addItem(td);
							}
						}
						
						fNewStatement = true;
					} else if (id.equals("function") || id.equals("task")) {
						SVDBTaskFuncScope f = parsers().functionParser().parse(
								start, modifiers);
						fScopeStack.peek().addItem(f);
						fNewStatement = true;
					}
				} else {
					System.out.println("[WARN] id @ top-level is null");
					System.out.println("    " + getLocation().getFileName()
							+ ":" + getLocation().getLineNo());
				}
			}
		} catch (EOFException e) {
		}
	}

	private void process_initial_always() throws SVParseException {
		String expr = "", name = "";
		
		String type = lexer().readKeyword("initial", "always");

		if (type.equals("always")) {
			if (lexer().peekOperator("@")) {
				lexer().eatToken();
				
				lexer().startCapture();

				if (lexer().peekOperator("(")) {
					lexer().skipPastMatch("(", ")");
				}
				expr = lexer().endCapture();
			} else if (lexer().peekOperator("#")) {
				lexer().eatToken();
				lexer().startCapture();

				if (lexer().peekOperator("(")) {
					lexer().skipPastMatch("(", ")");
				} else {
					// Just read to the end of the next whitespace item
					lexer().eatToken();
				}

				expr = lexer().endCapture();
			}
		}

		SVDBScopeItem scope;
		if (type.equals("always")) {
			scope = new SVDBAlwaysBlock(expr);
		} else {
			scope = new SVDBInitialBlock();
		}
		setLocation(scope);

		fScopeStack.peek().addItem(scope);
		fScopeStack.push(scope);
		

		if (lexer().peekKeyword("begin")) {
			parsers().behavioralBlockParser().parse();
		} else {
			// single-statement begin.
		}

		if (fScopeStack.size() > 0
				&& (fScopeStack.peek().getType() == SVDBItemType.AlwaysBlock || fScopeStack
						.peek().getType() == SVDBItemType.InitialBlock)) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop().setName(name);
		}
	}

	private void process_assign() throws SVParseException {
		String target = "";
		lexer().readKeyword("assign");

		if (lexer().peekId() || lexer().peekOperator("(")) {
			target = readExpression();
		} else if (lexer().peekOperator("{")) {
			lexer().startCapture();
			lexer().skipPastMatch("{", "}");
			target = lexer().endCapture();
		}

		SVDBAssign assign = new SVDBAssign(target);
		setLocation(assign);
		fScopeStack.peek().addItem(assign);
	}

	private void process_constraint() throws SVParseException {
		lexer().readKeyword("constraint");
		
		String cname = lexer().readId();

		if (lexer().peekOperator("{")) {
			lexer().startCapture();
			lexer().skipPastMatch("{", "}");
			String expr = lexer().endCapture();

			expr = expr.substring(1, expr.length() - 1);

			constraint(cname, expr);
		}

		fNewStatement = true;
	}

	private void process_covergroup() throws SVParseException {
		fSemanticScopeStack.push("covergroup");

		lexer().readKeyword("covergroup");
		String cg_name = lexer().readId();

		SVDBCoverGroup cg = new SVDBCoverGroup(cg_name);
		cg.setSuperClass(BuiltinClassConstants.Covergroup);
		setLocation(cg);
		fScopeStack.peek().addItem(cg);
		fScopeStack.push(cg);
		

		while (lexer().peekOperator("(")) {
			lexer().skipPastMatch("(", ")");
		}

		if (lexer().peekOperator("@")) {
			lexer().eatToken();
			
			/*
			if (ch == '@') {
				ch = skipWhite(get_ch());
			}
			 */
			if (lexer().peekOperator("(")) {
				lexer().skipPastMatch("(", ")");
			}
		}

		// Skip statements
		String id;
		while ((id = scan_statement()) != null) {
			fStartLocation = getStmtLocation();

			if (id.equals("endgroup")) {
				break;
			} else {
				// This is likely a coverpoint/coverpoint cross

				if (lexer().peekOperator(":")) {
					// yep...
					String name = id;

					String type = lexer().readKeyword("coverpoint", "cross");

					// Now, skip forward and try to read the target
					// read any expression character
					lexer().startCapture();
					while (!lexer().peekOperator("{", ";")) {
						lexer().eatToken();
					}
					String target = lexer().endCapture();

					/*
					if (target != null) {
						if (target.endsWith("{")) {
							target = target.substring(0, target.length() - 1);
						}
						target = target.trim();
					}
					 */

					String body = "";
					if (lexer().peekOperator("{")) {
						lexer().eatToken();
						lexer().startCapture();
						lexer().skipPastMatch("{", "}");
						body = lexer().endCapture();

						body = body.trim();
						if (body.endsWith("}")) {
							body = body.substring(0, body.length() - 1);
						}
					}

					// Update the end location
					setStmtLocation(getLocation());
					
					SVDBScopeItem it = null;

					if (type != null) {
						if (type.equals("coverpoint")) {
							SVDBCoverPoint cp = new SVDBCoverPoint(name, target, body);
							cp.setSuperClass(BuiltinClassConstants.Coverpoint);
							it = cp;
						} else if (type.equals("cross")) {
							SVDBCoverpointCross cpc = new SVDBCoverpointCross(name, body); 
							cpc.setSuperClass(BuiltinClassConstants.CoverpointCross);

							for (String cp : target.split(",")) {
								cp = cp.trim();
								if (!cp.equals("")) {
									if (cp.endsWith(";")) {
										cp = cp.substring(0, cp.length() - 1).trim();
									}
									cpc.getCoverpointList().add(cp);
								}
							}
						} else {
							// System.out.println("unknown covergroup item: " + type);
						}
					}

					if (it != null) {
						setStartLocation(it);
						setEndLocation(it);
						fScopeStack.peek().addItem(it);
					}
					
					fNewStatement = true;
				}
			}
		}
		
		cg.setEndLocation(lexer().getStartLocation());
		
		lexer().readKeyword("endgroup");
		if (lexer().peekOperator(":")) {
			lexer().eatToken();
			lexer().readId(); // labeled group
		}

		handle_leave_scope();
	}

	private void process_sequence() throws SVParseException {

		lexer().readKeyword("sequence");
		String name = lexer().readId();
		fSemanticScopeStack.push("sequence");

		SVDBScopeItem it = new SVDBScopeItem(name, SVDBItemType.Sequence);

		setLocation(it);
		fScopeStack.peek().addItem(it);
		fScopeStack.push(it);
		

		String id;
		while ((id = scan_statement()) != null) {
			if (id.equals("endsequence")) {
				break;
			}
		}

		handle_leave_scope();
	}

	private SVDBItem process_property() throws SVParseException {
		lexer().readKeyword("property");
		String name = lexer().readId();
		fSemanticScopeStack.push("property");

		SVDBScopeItem it = new SVDBScopeItem(name, SVDBItemType.Property);

		setLocation(it);

		fScopeStack.peek().addItem(it);
		fScopeStack.push(it);

		String id;
		while ((id = scan_statement()) != null) {
			if (id.equals("endproperty")) {
				break;
			}
		}

		handle_leave_scope();

		return it;
	}

	private int scan_qualifiers(boolean param)
			throws EOFException {
		int modifiers = 0;
		Map<String, Integer> qmap = (param) ? fTaskFuncParamQualifiers
				: fFieldQualifers;

		String id;
		while ((id = lexer().peek()) != null && qmap.containsKey(id)) {
			debug("item modified by \"" + id + "\"");
			modifiers |= qmap.get(id);

			lexer().eatToken();
		}

		return modifiers;
	}

	public String scopedIdentifier(boolean allow_keywords) throws SVParseException {
		StringBuilder id = new StringBuilder();

		if (!allow_keywords) {
			id.append(lexer().readId());
		} else if (lexer().peekKeyword() || lexer().peekId()) {
			id.append(lexer().eatToken());
		} else {
			error("scopedIdentifier: starts with " + lexer().peek());
		}

		while (lexer().peekOperator("::")) {
			id.append("::");
			lexer().eatToken();
			if (lexer().peekKeyword("new") ||
					(allow_keywords && lexer().peekKeyword())) {
				id.append(lexer().readKeyword());
			} else {
				id.append(lexer().readId());
			}
		}

		return id.toString();
	}

	/*
	private SVDBItem process_interface_module_class()
			throws SVParseException {
		SVDBItem it = null;
		String id;
		List<SVClassIfcModParam> params = null;
		String super_name = null;
		List<SVClassIfcModParam> super_params = null;
		String module_type_name = null;
		String ports = null;
		String type = lexer().eatToken();

		debug("--> process_module()");

		fSemanticScopeStack.push(type);

		//
		// Skip up to point of module type name
		//

		if (lexer().peekId()) {
			module_type_name = lexer().readId();
		} else {
			return it; // TODO: ?
		}

		// Handle modules with parameters
		if (lexer().peekOperator("#")) {
			if (lexer().peekOperator("(")) {
				lexer().startCapture();
				lexer().skipPastMatch("(", ")");
				String p_str = lexer().endCapture();

				params = parse_parameter_str(p_str);
			}
		}

		if (params == null) {
			params = new ArrayList<SVClassIfcModParam>();
		}

		// Class extension
		if (type.equals("class")) {
			if (lexer().peekKeyword("extends")) {
				lexer().eatToken();
				// likely an 'extends' statement
				super_name = lexer().readId();

				if (lexer().peekOperator("#")) {
					// parameters
					lexer().readOperator("(");
					lexer().startCapture();
					lexer().skipPastMatch("(", ")");
					String p_str = lexer().endCapture();

					super_params = parse_parameter_str(p_str);
				}
			}
			lexer().readOperator(";");
		} else if (type.equals("module")) {
			// Module port-list
			if (lexer().peekOperator("(")) {
				lexer().startCapture();
				lexer().skipPastMatch("(", ")");
				ports = lexer().endCapture();
			}
		}

		if (type.equals("module") || type.equals("macromodule") ||
				type.equals("interface") || type.equals("program")) {
			SVDBModIfcClassDecl cls = new SVDBModIfcClassDecl(module_type_name,
					SVDBItemType.Module);
			fScopeStack.peek().addItem(cls);
			fScopeStack.push(cls);

			setLocation(cls);
			it = cls;
		} else if (type.equals("program")) {
			SVDBModIfcClassDecl p = new SVDBModIfcClassDecl(
					module_type_name, SVDBItemType.Program);

			fScopeStack.peek().addItem(p);
			fScopeStack.push(p);

			setLocation(p);
			it = p;
		} else if (type.equals("interface")) {
			SVDBModIfcClassDecl ifc = new SVDBModIfcClassDecl(module_type_name,
					SVDBItemType.Interface);
			fScopeStack.peek().addItem(ifc);
			fScopeStack.push(ifc);

			setLocation(ifc);
			it = ifc;
		} else if (type.equals("class")) {
			System.out
					.println("[ERROR] should not be calling enter_class_decl");
			SVDBModIfcClassDecl decl = new SVDBModIfcClassDecl(
					module_type_name, SVDBItemType.Class);

			for (SVClassIfcModParam p : params) {
				SVDBModIfcClassParam p_svdb = new SVDBModIfcClassParam(p
						.getName());
				p_svdb.setDefault(p.getDefault());
				decl.getParameters().add(p_svdb);
			}

			decl.setSuperClass(super_name);

			if (super_params != null) {
				for (SVClassIfcModParam p : super_params) {
					decl.getSuperParameters().add(
							new SVDBModIfcClassParam(p.getName()));
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
			SVDBItem item = process_module_class_interface_body_item(type);

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
	 */

	private void process_struct_decl(SVTypeInfo type_info)
			throws SVParseException {

		while (lexer().peekId()) {
			lexer().eatToken();
		}

		if (!lexer().peekOperator("{")) {
			return;
		}

		// Add struct declaration
		SVDBModIfcClassDecl decl = new SVDBModIfcClassDecl("",
				SVDBItemType.Struct);
		fScopeStack.peek().addItem(decl);
		fScopeStack.push(decl);
		setLocation(decl);

		while (scan_statement() != null) {
			SVDBItem item = 
				process_module_class_interface_body_item("struct");

			if (item == null) {
				break;
			}

			// Add the item to the struct declaration
			fScopeStack.peek().addItem(item);

			// Recognize when we've reached the end of the
			// struct definition
			if (lexer().peekOperator(";")) {
				lexer().eatToken();
				if (lexer().peekOperator("}")) {
					break;
				}
			}
		}

		if (type_info == null) {
			fStmtLocation = getLocation();
			leave_struct_decl("ANONYMOUS");
		}
	}

	private void process_package(String id) throws SVParseException {
		if (id.equals("package")) {
			lexer().readKeyword("package");
			String pkg = readQualifiedIdentifier();
			enter_package(pkg);
		} else {
			leave_package();
		}
	}

	public void enter_scope(String type, SVDBScopeItem scope) {
		fSemanticScopeStack.push(type);
		fScopeStack.peek().addItem(scope);
		fScopeStack.push(scope);
	}

	public void handle_leave_scope() {
		handle_leave_scope(1);
	}

	private void handle_leave_scope(int levels) {
		fStmtLocation = getLocation();
		for (int i = 0; i < levels; i++) {
			String type = null;

			if (fSemanticScopeStack.size() > 0) {
				type = fSemanticScopeStack.pop();
			} else {
				System.out.println("[ERROR] attempting to leave scope @ "
						+ getLocation().getFileName() + ":"
						+ getLocation().getLineNo());
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
					if (fScopeStack.size() > 0
							&& fScopeStack.peek().getType() == SVDBItemType.Sequence) {
						setEndLocation(fScopeStack.peek());
						fScopeStack.pop();
					}
				} else if (type.equals("property")) {
					if (fScopeStack.size() > 0
							&& fScopeStack.peek().getType() == SVDBItemType.Property) {
						setEndLocation(fScopeStack.peek());
						fScopeStack.pop();
					}
				}
			}
		}
	}

	List<SVClassIfcModParam> parse_parameter_str(String p_str) {
		List<SVClassIfcModParam> ret = new ArrayList<SVClassIfcModParam>();
		ITextScanner in = new StringTextScanner(new StringBuilder(p_str));
		/*
		 * SVScannerInput in = new SVScannerInput("param_processor", new
		 * StringInputStream(p_str), null, fObserver, fDefineProvider);
		 */
		int ch = 0;
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

	private void process_import() throws SVParseException {
		SVDBLocation start = lexer().getStartLocation();
		lexer().readKeyword("import");
		
		if (lexer().peekString()) {
			// likely DPI import/export. Double-check
			String qualifier = lexer().readString();

			if (qualifier != null && qualifier.equals("DPI")
					|| qualifier.equals("DPI-C")) {
				int modifiers = IFieldItemAttr.FieldAttr_DPI;

				modifiers |= scan_qualifiers(false);

				// id = lexer().readId();

				// Read tf extern declaration
				SVDBTaskFuncScope tf = parsers().functionParser().parse(start, modifiers);
				fScopeStack.peek().addItem(tf);
				fNewStatement = true;
			}
		} else { // if (type.equals("import")) {
			// skip to end-of-statement
			lexer().startCapture();
			while (lexer().peek() != null && !lexer().peekOperator(";")) {
				lexer().eatToken();
			}
			String imp_str = lexer().endCapture();

			import_statment(imp_str);
		}
	}

	private void process_export(String type) throws SVParseException {
		String qualifier = lexer().read();

		if (qualifier != null && qualifier.equals("DPI")
				|| qualifier.equals("DPI-C")) {

			String kind = lexer().readId();
			String id = lexer().readId();

			if (kind != null && id != null) {

			}
		}
	}

	public List<SVDBTypedef> process_typedef(boolean have_typedef_kw) throws SVParseException {
		List<SVDBTypedef> typedef_list = new ArrayList<SVDBTypedef>();

		// typedef <type> <name>;

		// SVTypeInfo type = readTypeName(false);
		SVDBLocation start = lexer().getStartLocation();
		// Don't try to read-ahead if we already know we've seen "typedef"
		if (!have_typedef_kw) {
			lexer().readKeyword("typedef");
		}
		SVDBTypeInfo type = parsers().dataTypeParser().data_type(0, lexer().eatToken());
		
		if (type.getDataType() != SVDBDataType.FwdDecl) {
			while (lexer().peek() != null) {
				String id = lexer().readId();
				
				if (lexer().peekOperator("[")) {
					// TODO: dimension
					lexer().skipPastMatch("[", "]");
				}

				SVDBTypedef typedef = new SVDBTypedef(type, id);

				typedef_list.add(typedef);
				typedef.setLocation(start);
				/*
				if (fScopeStack.size() > 0) {
					fScopeStack.peek().addItem(typedef);
				}
				 */
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		} else {
			SVDBTypedef typedef = new SVDBTypedef(type, type.getName());
			typedef_list.add(typedef);
			typedef.setLocation(start);
		}

		lexer().readOperator(";");
		
		return typedef_list;
	}

	static private final Map<String, Integer> fFieldQualifers;
	static private final Map<String, Integer> fTaskFuncParamQualifiers;
	static {
		fFieldQualifers = new HashMap<String, Integer>();
		fFieldQualifers.put("local", IFieldItemAttr.FieldAttr_Local);
		fFieldQualifers.put("static", IFieldItemAttr.FieldAttr_Static);
		fFieldQualifers
				.put("protected", IFieldItemAttr.FieldAttr_Protected);
		fFieldQualifers.put("virtual", IFieldItemAttr.FieldAttr_Virtual);
		fFieldQualifers
				.put("automatic", IFieldItemAttr.FieldAttr_Automatic);
		fFieldQualifers.put("rand", IFieldItemAttr.FieldAttr_Rand);
		fFieldQualifers.put("randc", IFieldItemAttr.FieldAttr_Randc);
		fFieldQualifers.put("extern", IFieldItemAttr.FieldAttr_Extern);
		fFieldQualifers.put("const", IFieldItemAttr.FieldAttr_Const);
		fFieldQualifers.put("pure", IFieldItemAttr.FieldAttr_Pure);
		fFieldQualifers.put("context", IFieldItemAttr.FieldAttr_Context);
		fFieldQualifers.put("__sv_builtin",
				IFieldItemAttr.FieldAttr_SvBuiltin);

		fTaskFuncParamQualifiers = new HashMap<String, Integer>();
		fTaskFuncParamQualifiers.put("pure", 0); // TODO
		fTaskFuncParamQualifiers.put("virtual",
				SVDBParamPort.FieldAttr_Virtual);
		fTaskFuncParamQualifiers.put("input",
				SVDBParamPort.Direction_Input);
		fTaskFuncParamQualifiers.put("output",
				SVDBParamPort.Direction_Output);
		fTaskFuncParamQualifiers.put("inout",
				SVDBParamPort.Direction_Inout);
		fTaskFuncParamQualifiers.put("ref", SVDBParamPort.Direction_Ref);
		fTaskFuncParamQualifiers.put("var", SVDBParamPort.Direction_Var);
	}

	private static SVDBItem fSpecialNonNull = new SVDBItem("SPECIAL_NON_NULL",
			SVDBItemType.VarDecl);

	public SVDBItem process_module_class_interface_body_item(String scope) throws SVParseException {
		int ch = -1, modifiers = 0;
		SVDBItem ret = null;
		String id = lexer().peek();

		debug("--> process_module_class_interface_body_item: \"" + id + "\"");

		// Ignore modifiers for now
		// lexer().next_token(); // ch = skipWhite(get_ch());
		
		// Save the start location before qualifiers
		SVDBLocation start = lexer().getStartLocation();

		// unget_ch(ch);
		modifiers = scan_qualifiers(false);
		// ch = skipWhite(get_ch());

		id = lexer().peek();

		if (id == null) {
			System.out.println("[ERROR] id=null @ "
					+ getStmtLocation().getFileName() + ":"
					+ getStmtLocation().getLineNo());
			return ret;
		}

		debug("body item is: " + id);

		if (id.equals("function") || id.equals("task")) {
			ret = parsers().functionParser().parse(start, modifiers);
			fScopeStack.peek().addItem(ret);
			fNewStatement = true;
		} else if (id.equals("property")) {
			ret = process_property();
			fNewStatement = true;
		} else if (id.equals("always") || id.equals("initial")) {
			process_initial_always();
			ret = fSpecialNonNull;
			fNewStatement = true;
		} else if (id.equals("modport")) {
			// TODO: shouldn't just skip
			lexer().eatToken();
			lexer().readId(); // modport name
			
			lexer().skipPastMatch("(", ")");
			lexer().readOperator(";");
			ret = fSpecialNonNull;
			fNewStatement = true;
		} else if (id.equals("assign")) {
			process_assign();
			ret = fSpecialNonNull;
			fNewStatement = true;
		} else if (id.equals("constraint")) {
			process_constraint();
			ret = fSpecialNonNull;
			fNewStatement = true;
		} else if (id.equals("covergroup")) {
			process_covergroup();
			ret = fSpecialNonNull;
			fNewStatement = true;
		} else if (id.equals("sequence")) {
			process_sequence();
			ret = fSpecialNonNull;
			fNewStatement = true;
		} else if (id.equals("import")) {
			process_import();
			ret = fSpecialNonNull;
			fNewStatement = true;
		} else if (id.equals("clocking")) {
			// Ignore this
			while ((id = scan_statement()) != null) {
				if (id.equals("endclocking")) {
					break;
				}
			}
			lexer().readKeyword("endclocking");
			ret = fSpecialNonNull;
			fNewStatement = true;
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
			for (SVDBTypedef td : process_typedef(false)) {
				if (fScopeStack.size() > 0) {
					fScopeStack.peek().addItem(td);
				}
			}
			
			ret = fSpecialNonNull;
			fNewStatement = true;
		} else if (id.equals("class") && !scope.equals("class")) {
			SVDBModIfcClassDecl cls = null;
			try {
				cls = parsers().classParser().parse(modifiers);
			} catch (SVParseException e) {
				System.out.println("ParseException: post-class-module()");
				e.printStackTrace();
			}
			ret = cls;
			fNewStatement = true;
		} else if (isFirstLevelScope(id, modifiers)) {
			// We've hit a first-level qualifier. This probably means that
			// there is a missing
			fNewStatement = true;
			ret = null;
		} else if (ch == ':') {
			// Labeled statement -- often a cover
			System.out.println("labeled statement: " + id);
			System.out.println("    " + getLocation().getFileName() + ":"
					+ getLocation().getLineNo());
			fNewStatement = true;
			ret = null;
		} else {
			// likely a variable or module declaration

			debug("Likely VarDecl: " + id);

			scanVariableDeclaration(modifiers);
			ret = fSpecialNonNull;
		}

		debug("<-- process_module_class_interface_body_item - " + ret);

		return ret;
	}

	/**
	 * scanVariableDeclaration()
	 * 
	 * Scans through a list of variable declarations
	 * 
	 * Expects first string(s) read to be the type name
	 */
	private boolean scanVariableDeclaration(int modifiers)
			throws SVParseException {
		List<SvVarInfo> vars = new ArrayList<SvVarInfo>();
		SVDBTypeInfo type;
		boolean is_variable = true;

		// TODO: need to modify this to be different for class and module/interface
		// scopes
		type = parsers().dataTypeParser().data_type(modifiers, lexer().eatToken());
		
		if (type == null) {
			error("Failed to parse type");
		}

		// bail out if there's an error
		/*
		if (type == null || type.fTypeName == null
				|| type.fTypeName.equals("begin")
				|| type.fTypeName.equals("end")) {
			return false;
		}
		 */

		// First, skip qualifiers
		/*
		 * if (ch == '#') { ch = skipWhite(get_ch());
		 * 
		 * if (ch == '(') { ch = skipPastMatch("()"); ch = skipWhite(ch); } }
		 * 
		 * if (ch == '[') { ch = skipPastMatch("[]"); ch = skipWhite(ch); }
		 */
		
		// Not a variable declaration
		if (lexer().peekOperator()) {
			return false;
		}

		// Handle parameterization
		do {

			if (lexer().peekOperator(",")) {
				lexer().eatToken();
			}

			String inst_name_or_var = lexer().readId();

			if (inst_name_or_var == null) {
				is_variable = false;
				break;
			}

			debug("inst name or var: " + inst_name_or_var);

			SvVarInfo var_info = new SvVarInfo();
			var_info.fName = inst_name_or_var;
			vars.add(var_info);

			if (lexer().peekOperator("(")) {
				type = new SVDBTypeInfoUserDef(type.getName(), SVDBDataType.ModuleIfc);
				
				// TODO:
				// type.fModIfc = true;

				// it's a module
				debug("module instantation - " + inst_name_or_var);
				lexer().skipPastMatch("(", ")");

				/*
				if (ch == ';') {
					unget_ch(ch);
				}
				 */
				break;
			} else if (lexer().peekOperator("[")) {
				// Array type
				lexer().startCapture();
				lexer().skipPastMatch("[", "]");
				String bounds = lexer().endCapture();

				bounds = bounds.substring(0, bounds.length() - 1).trim();

				if (bounds != null) {
					// remove ']'
					bounds = bounds.substring(0, bounds.length() - 1);
					bounds = bounds.trim();

					if (bounds.startsWith("$")) {
						var_info.fAttr |= SvVarInfo.Attr_Queue;
					} else if (bounds.equals("")) {
						var_info.fAttr |= SvVarInfo.Attr_DynamicArray;
					} else {
						// TODO: Don't really know. Could be a fixed-size array
						// or
						// a fixed-size array
						if (bounds.equals("*")) {
							var_info.fAttr |= SvVarInfo.Attr_AssocArray;
						} else {
							var_info.fArrayDim = bounds;
						}
					}
				}
			}

		} while (lexer().peekOperator(","));

		if (vars.size() > 0) {
			variable_decl(type, modifiers, vars);
		}

		return is_variable;
	}

	public static boolean isFirstLevelScope(String id, int modifiers) {
		return (id.equals("class")
				||
				// virtual interface is a valid field
				(id.equals("interface") && (modifiers & ISVScannerObserver.FieldAttr_Virtual) == 0)
				|| id.equals("module"));
	}

	public static boolean isSecondLevelScope(String id) {
		return (id.equals("task") || id.equals("function")
				|| id.equals("always") || id.equals("initial"));
	}

	/**
	 * scan_statement()
	 */
	public String scan_statement() {
		String id;

		lexer().setNewlineAsOperator(true);
		// System.out.println("--> scan_statement() " + lexer().peek() + "\n");

		while ((id = lexer().peek()) != null) {
			/*
			System.out.println("scan_statement: id=\"" + id
					+ "\" ; NewStatement=" + fNewStatement);
			 */
			if (!fNewStatement && (id.equals(";") || id.equals("\n")
					|| (SVKeywords.isSVKeyword(id) && id.startsWith("end")))) {
				fNewStatement = true;
				lexer().eatToken();
			} else if (fNewStatement) {
				fStmtLocation = getLocation();
				if (SVCharacter.isSVIdentifierStart(id.charAt(0))) {
					fNewStatement = false;
					break;
				} else if (id.charAt(0) == '`') {
					System.out
							.println("[ERROR] pre-processor directive encountered");
					fNewStatement = true;
				}
			}
			lexer().eatToken();
		}

		// System.out.println("<-- scan_statement() - " + id + "\n");
		lexer().setNewlineAsOperator(false);
		return id;
	}
	
	public void setNewStatement() {
		fNewStatement = true;
	}

	/*
	 * Currently unused private String readLine(int ci) throws EOFException { if
	 * (fInputStack.size() > 0) { return fInputStack.peek().readLine(ci); } else
	 * { return ""; } }
	 */

	private String readQualifiedIdentifier() throws SVParseException {
		if (!lexer().peekId() && !lexer().peekKeyword()) {
			return null;
		}
		StringBuffer ret = new StringBuffer();

		ret.append(lexer().eatToken());

		while (lexer().peekOperator("::")) {
			ret.append(lexer().eatToken());
			ret.append(lexer().eatToken());
		}
		/*
		while (lexer().peekId() || lexer().peekOperator("::") || lexer().peekKeyword()) {
			ret.append(lexer().eatToken());
		}
		 */

		return ret.toString();
	}
	
	private static final String fRecognizedOps[] = {
		"+", "-", "^", "|",  "&", "*", "?", ".", ":", "::", "#", "'",
		"%", "**", "<<", ">>", "<", ">"
	};

	public String readExpression() throws SVParseException {
		lexer().startCapture();
		while (lexer().peek() != null) {
			if (lexer().peekOperator("(")) {
				lexer().skipPastMatch("(", ")");
			} else if (lexer().peekOperator("{")) {
				lexer().skipPastMatch("{", "}");
			} else if (lexer().peekOperator("-")) {
				lexer().eatToken();
				if (lexer().peekOperator("(")) {
					lexer().skipPastMatch("(", ")");
				} else {
					lexer().eatToken();
				}
			} else if (!lexer().peekOperator()) {
				lexer().eatToken();
			} else {
				break;
			}

			if (lexer().peekOperator(fRecognizedOps)) {
				lexer().eatToken();
			} else if (lexer().peekOperator("(")) {
				lexer().skipPastMatch("(", ")");
			} else {
				break;
			}

			/*
			if (lexer().peekOperator(".", "::")) {
				lexer().eatToken();
			} else {
				break;
			}
			 */
		}
		return lexer().endCapture();
	}

	public ScanLocation getLocation() {
		return fInput.getLocation();
	}

	public void debug(String msg) {
		fLog.debug(msg);
	}

	public void error(String msg, String filename, int lineno) {
		SVDBMarkerItem marker = new SVDBMarkerItem(SVDBMarkerItem.MARKER_ERR,
				SVDBMarkerItem.KIND_GENERIC, msg);
		marker.setLocation(new SVDBLocation(lineno));

		fFile.addItem(marker);
	}

	public SVDBFile parse(InputStream in, String name) {
		fScopeStack.clear();

		
		fFile = new SVDBFile(name);
		fScopeStack.clear();
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
		fLexer.init(this, fInput);
	}

	public void enter_package(String name) {
		SVDBPackageDecl pkg_decl = new SVDBPackageDecl(name);

		setLocation(pkg_decl);

		fScopeStack.peek().addItem(pkg_decl);
		fScopeStack.push(pkg_decl);
	}

	public void leave_package() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.PackageDecl) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void import_statment(String imp) throws HaltScanException {
		// TODO Auto-generated method stub

	}

	public void leave_interface_decl() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Interface) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void leave_class_decl() throws HaltScanException {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Class) {
//			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void leave_struct_decl(String name) throws HaltScanException {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Struct) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop().setName(name);
		}
	}

	public void leave_task_decl() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Task) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void leave_func_decl() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Function) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void init(ISVScanner scanner) {
		// TODO Auto-generated method stub
	}

	public void leave_module_decl() throws HaltScanException {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Module) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void leave_program_decl() throws HaltScanException {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Program) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void variable_decl(SVDBTypeInfo type, int attr,
			List<SvVarInfo> variables) throws HaltScanException {

		if (type.getDataType() == SVDBDataType.ModuleIfc) {
			SVDBModIfcInstItem item = new SVDBModIfcInstItem(type,
					variables.get(0).fName);
			setLocation(item);
			fScopeStack.peek().addItem(item);
		} else {
			/*
			SVDBParamValueAssignList parameters = null;

			if (type.fParameters != null && type.fParameters.size() > 0) {
				parameters = new SVDBParamValueAssignList();
				for (SVClassIfcModParam p : type.fParameters) {
					parameters.addParameter(new SVDBParamValueAssign("", p
							.getName()));
				}
			}

			int type_attr = 0;

			if (type.fVectorDim != null) {
				type_attr |= SVDBTypeInfo.TypeAttr_Vectored;
			}

			SVDBTypeInfo type_info = null;
			String typename = type.fTypeName;
			if (typename.indexOf('[') != -1) {
				typename = typename.substring(0, typename.indexOf('[')).trim();
			}
			 */

			for (SvVarInfo var : variables) {
				if (var != null) {

					/*
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
					 */

					// type_info = new SVDBTypeInfo(type.fTypeName,
					// type_attr|var.fAttr);
					SVDBVarDeclItem item = new SVDBVarDeclItem(type,
							var.fName, var.fAttr);
					item.setArrayDim(var.fArrayDim);
					setLocation(item);

					if (item.getName() == null || item.getName().equals("")) {
						System.out.println("    " +
								fFile.getFilePath() + ":"  + item.getLocation().getLine());
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
			item.setLocation(new SVDBLocation(loc.getLineNo()));
		}
	}

	private void setLocation(SVDBItem item) {
		ScanLocation loc = getStmtLocation();
		item.setLocation(new SVDBLocation(loc.getLineNo()));
	}

	private void setEndLocation(SVDBScopeItem item) {
		ScanLocation loc = getStmtLocation();
		item.setEndLocation(new SVDBLocation(loc.getLineNo()));
	}

	public void preproc_define(String key, List<String> params, String value) {
		SVDBMacroDef def = new SVDBMacroDef(key, params, value);

		setLocation(def);

		if (def.getName() == null || def.getName().equals("")) {
			// TODO: find filename
			System.out.println("    <<UNKNOWN>> " + ":" + def.getLocation().getLine());
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

	public void leave_preproc_conditional() {
	}

	public void comment(String comment) {

	}

	public void leave_covergroup() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Covergroup) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void constraint(String name, String expr) {
		SVDBConstraint c = new SVDBConstraint(name, expr);
		setLocation(c);
		fScopeStack.peek().addItem(c);
	}

	public void enter_sequence(String name) {
	}

	public boolean error_limit_reached() {
		return (fParseErrorMax > 0 && fParseErrors.size() >= fParseErrorMax);
	}

	public SVLexer lexer() {
		return fLexer;
	}

	public void warning(String msg, int lineno) {
		System.out.println("[FIXME] warning \"" + msg + "\" @ " + lineno);
	}

	public void error(SVParseException e) throws SVParseException {
		fParseErrors.add(e);

		
		error(e.getMessage(), e.getFilename(), e.getLineno());
		
		// Send the full error forward
		fLog.debug("Parse Error: " + e.getMessage() + " " + 
				e.getFilename() + ":" + e.getLineno(), e);
		
		throw e;
	}
	
	public void error(String msg) throws SVParseException {
		error(SVParseException.createParseException(msg, 
				fFile.getFilePath(), getLocation().getLineNo()));
	}

	public SVParsers parsers() {
		return fSVParsers;
	}

	public void enter_file(String filename) {
		// TODO Auto-generated method stub
		
	}

	public void leave_file() {
		// TODO Auto-generated method stub
		
	}

}
