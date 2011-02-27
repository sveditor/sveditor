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

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBAlwaysBlock;
import net.sf.sveditor.core.db.SVDBAssign;
import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.SVDBCoverGroup;
import net.sf.sveditor.core.db.SVDBDataType;
import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBGenerateBlock;
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
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltin;
import net.sf.sveditor.core.db.SVDBTypeInfoBuiltinNet;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.db.stmt.SVDBParamPort;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.IDefineProvider;
import net.sf.sveditor.core.scanner.IPreProcErrorListener;
import net.sf.sveditor.core.scanner.ISVPreProcScannerObserver;
import net.sf.sveditor.core.scanner.ISVScanner;
import net.sf.sveditor.core.scanner.SVCharacter;
import net.sf.sveditor.core.scanner.SVKeywords;
import net.sf.sveditor.core.scanner.SVPreProcScanner;
import net.sf.sveditor.core.scanner.SVScannerTextScanner;
import net.sf.sveditor.core.scanutils.ScanLocation;

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
		error(msg, filename, lineno, -1);
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
						try {
							parsers().classParser().parse(modifiers);
						} catch (SVParseException e) {}
						fNewStatement = true;
					} else if (id.equals("module") || id.equals("macromodule") ||
							id.equals("interface") || id.equals("program")) {
						// enter module scope
						// TODO: should probably add this item to the 
						// File scope here
						try {
							parsers().modIfcProgParser().parse(modifiers);
						} catch (SVParseException e) {}
					} else if (id.equals("package") || id.equals("endpackage")) {
						process_package(id);
					} else if (id.equals("import")) {
						List<SVDBItem> items = parsers().importParser().parse();
						
						if (fScopeStack.size() > 0) {
							for (SVDBItem item : items) {
								fScopeStack.peek().addItem(item);
							}
						}
						fNewStatement = true;
					} else if (id.equals("export")) {
						process_export(id);
					} else if (id.equals("typedef")) {
						SVDBTypedefStmt td = parsers().dataTypeParser().typedef();
						if (fScopeStack.size() > 0) {
							fScopeStack.peek().addItem(td);
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
		
		String type = lexer().readKeyword("initial", 
				"always", "always_comb", "always_latch", "always_ff");

		if (!type.equals("initial")) {
			if (lexer().peekOperator("@")) {
				lexer().eatToken();
				
				if (lexer().peekOperator("*")) {
					lexer().eatToken();
					expr = "*";
				} else {
					lexer().startCapture();

					if (lexer().peekOperator("(")) {
						lexer().skipPastMatch("(", ")");
					}
					expr = lexer().endCapture();
				}
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
		if (type.startsWith("always")) {
			scope = new SVDBAlwaysBlock(expr);
		} else {
			scope = new SVDBInitialBlock();
		}
		setLocation(scope);

		fScopeStack.peek().addItem(scope);
		fScopeStack.push(scope);
		
		parsers().behavioralBlockParser().statement();

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
		
		if (lexer().peekOperator("#")) {
			// Time expression
			lexer().eatToken();
			parsers().exprParser().expression(); // delay expression
		}
		
		// Allow LHS to be a SV keyword (fits Verilog)
		if (lexer().peekId() || lexer().peekOperator("(") ||
				(lexer().peekKeyword() && !SVKeywords.isVKeyword(lexer().peek()))) {
			target = parsers().exprParser().expression().toString();
		} else if (lexer().peekOperator("{")) {
			lexer().startCapture();
			lexer().skipPastMatch("{", "}");
			target = lexer().endCapture();
		}
		
		SVDBAssign assign = new SVDBAssign(target);
		
		if (lexer().peekOperator("=")) {
			lexer().eatToken();
			parsers().exprParser().expression();
		}
		
		setLocation(assign);
		fScopeStack.peek().addItem(assign);
		lexer().readOperator(";");
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

	public int scan_qualifiers(boolean param)
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

	private void process_package(String id) throws SVParseException {
		if (id.equals("package")) {
			SVDBLocation start = lexer().getStartLocation();
			lexer().readKeyword("package");
			String pkg = readQualifiedIdentifier();
			
			SVDBPackageDecl pkg_decl = new SVDBPackageDecl(pkg);
			pkg_decl.setLocation(start);

			fScopeStack.peek().addItem(pkg_decl);
			fScopeStack.push(pkg_decl);
		} else {
			SVDBLocation end = lexer().getStartLocation();
			if (fScopeStack.size() > 0
					&& fScopeStack.peek().getType() == SVDBItemType.PackageDecl) {
				fScopeStack.peek().setEndLocation(end);
				fScopeStack.pop();
			}
			lexer().readKeyword("endpackage");
			setNewStatement();
			
			// Handled named package end-block
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				lexer().readId();
			}
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
				} else {
					fScopeStack.pop();
				}
			}
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

	private static SVDBItem fSpecialNonNull = new SVDBItem("SPECIAL_NON_NULL", SVDBItemType.VarDeclStmt);

	public ISVDBItemBase process_module_class_interface_body_item(String scope) throws SVParseException {
		int ch = -1, modifiers = 0;
		ISVDBItemBase ret = null;
		String id = lexer().peek();

		debug("--> process_module_class_interface_body_item: \"" + id + 
				"\" @ " + lexer().getStartLocation().getLine());

		// Save the start location before qualifiers
		SVDBLocation start = lexer().getStartLocation();
		modifiers = scan_qualifiers(false);

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
			fScopeStack.peek().addItem((SVDBTaskFuncScope)ret);
			fNewStatement = true;
		} else if (id.equals("property")) {
			ret = process_property();
			fNewStatement = true;
		
		// Generate-block statements
		} else if (id.equals("generate")) {
			ret = parsers().generateBlockParser().generate_block();
			fScopeStack.peek().addItem((SVDBGenerateBlock)ret);
			fNewStatement = true;
		} else if (id.equals("for")) {
			ret = parsers().generateBlockParser().for_block();
			fNewStatement = true;
		} else if (id.equals("if")) {
			ret = parsers().generateBlockParser().if_block();
			fNewStatement = true;
		} else if (id.equals("case")) {
			ret = parsers().generateBlockParser().case_block();
			fNewStatement = true;
		} else if (id.equals("specify")) {
			ret = parsers().specifyBlockParser().parse();
			ret = fSpecialNonNull;
			fNewStatement = true;
		} else if (id.equals("default") || id.equals("global") || id.equals("clocking")) {
			// Clocking block
			ret = parsers().clockingBlockParser().parse();
			fNewStatement = true;
		} else if (id.equals(";")) {
			// null statement
			System.out.println("null statement");
			lexer().eatToken();
			fNewStatement = true;
			ret = fSpecialNonNull;
		} else if (id.equals("always") || id.equals("always_comb") ||
				id.equals("always_latch") || id.equals("always_ff") ||
				id.equals("initial")) {
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
			SVDBCoverGroup cg = parsers().covergroupParser().parse();
			if (fScopeStack.size() > 0) {
				fScopeStack.peek().addItem(cg);
			}
			ret = cg;
			fNewStatement = true;
		} else if (id.equals("sequence")) {
			process_sequence();
			ret = fSpecialNonNull;
			fNewStatement = true;
		} else if (id.equals("import")) {
			List<SVDBItem> items = parsers().importParser().parse();
			
			if (fScopeStack.size() > 0) {
				for (SVDBItem item : items) {
					fScopeStack.peek().addItem(item);
				}
			}
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
			SVDBTypedefStmt td = parsers().dataTypeParser().typedef();
			if (fScopeStack.size() > 0) {
				fScopeStack.peek().addItem(td);
			}
			
			ret = td;
			fNewStatement = true;
		} else if ((id.equals("class") && !scope.equals("class"))) {
			SVDBClassDecl cls = null;
			try {
				cls = parsers().classParser().parse(modifiers);
			} catch (SVParseException e) {
//				System.out.println("ParseException: post-class-module()");
//				e.printStackTrace();
			}
			ret = cls;
			fNewStatement = true;
		} else if (id.equals("module") || id.equals("program") ||
				(id.equals("interface") && (modifiers & SVDBFieldItem.FieldAttr_Virtual) == 0)) {
			SVDBModIfcClassDecl m = null;
			// enter module scope
			// TODO: should probably add this item to the 
			// File scope here
			try {
				m = parsers().modIfcProgParser().parse(modifiers);
			} catch (SVParseException e) {
			}
			
			ret = m;
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
		} else if (id.equals("parameter") || id.equals("localparam")) {
			// local parameter
			lexer().eatToken();
			
			if (lexer().peekKeyword("type")) {
				lexer().eatToken();
			}
			SVDBTypeInfo data_type = parsers().dataTypeParser().data_type(0);
			String param_name;
			
			SVDBLocation it_start = lexer().getStartLocation();
			
			if (lexer().peekId()) {
				// likely a typed parameter
				param_name = lexer().readId();
			} else {
				// likely an untyped parameter
				param_name = data_type.getName();
				data_type = null;
			}
			
			SVDBParamPort p = new SVDBParamPort(data_type);
			SVDBVarDeclItem pi;
			while (true) {
				if (lexer().peekOperator("=")) {
					lexer().eatToken();
					parsers().exprParser().expression();
				}
				
				pi = new SVDBVarDeclItem(param_name);
				pi.setLocation(it_start);
				p.addVar(pi);
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
					it_start = lexer().getStartLocation();
					param_name = lexer().readId();
				} else {
					break;
				}
			}
			if (fScopeStack.size() > 0) {
				fScopeStack.peek().addItem(p);
			}
			lexer().readOperator(";");
			fNewStatement = true;
			ret = fSpecialNonNull;
		} else if (SVDataTypeParser.NetType.contains(id)) {
			// net type
			String net_type = lexer().eatToken();
			String vector_dim = null;
			SVDBVarDeclStmt var = null;
			String net_name = null;
			SVDBTypeInfoBuiltinNet type_info = null;
			SVDBTypeInfo data_type = null;
			
			debug("Net Type: " + net_type + " @ " + 
					lexer().getStartLocation().getLine());
			
			// vectored untyped net
			if (lexer().peekOperator("[")) {
				data_type = new SVDBTypeInfoBuiltin(net_type);
				lexer().startCapture();
				lexer().skipPastMatch("[", "]");
				vector_dim = lexer().endCapture();
				((SVDBTypeInfoBuiltin)data_type).setVectorDim(vector_dim);
				net_name = lexer().readId();
			} else {
				data_type = parsers().dataTypeParser().data_type(0);

				// Now, based on what we see next, we determine whether the
				// net is typed or untyped

				if (lexer().peekOperator(",", ";", "=")) {
					// The net was untyped
					net_name = data_type.getName();
					data_type = new SVDBTypeInfoBuiltin(net_type);
				} else {
					// Assume the net to be typed
					net_name = lexer().readId();
				}
			}
			type_info = new SVDBTypeInfoBuiltinNet(net_type, data_type);
			
			var = new SVDBVarDeclStmt(type_info, 0);
			var.setLocation(start);
			while (true) {
				SVDBVarDeclItem vi = new SVDBVarDeclItem(net_name);
				var.addVar(vi);
				
				if (lexer().peekOperator("[")) {
					vi.setArrayDim(parsers().dataTypeParser().var_dim());
				}
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
					net_name = lexer().readId();
				} else if (lexer().peekOperator("=")) {
					// Initialized wire
					lexer().eatToken();
					parsers().exprParser().expression();
				} else {
					break;
				}
			}
			
			if (fScopeStack.size() > 0) {
				fScopeStack.peek().addItem(var);
			}
			
			lexer().readOperator(";");
			fNewStatement = true;
			ret = fSpecialNonNull;
		} else if (lexer().peekKeyword(SVKeywords.fBuiltinGates)) {
			List<SVDBModIfcInstItem> insts = parsers().gateInstanceParser().parse();
			// TODO: add to hierarchy (?)
			fNewStatement = true;
			ret = fSpecialNonNull;
		} else if (lexer().peekKeyword("defparam", "specparam")) {
			// TODO: defparam doesn't appear in hierarchy
			lexer().eatToken();
			while (lexer().peek() != null && !lexer().peekOperator(";")) {
				parsers().exprParser().expression();
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
			lexer().readOperator(";");
			fNewStatement = true;
			ret = fSpecialNonNull;
		} else if (!lexer().peekOperator()) {
			// likely a variable or module declaration

			debug("Likely VarDecl: " + id);

			scanVariableDeclaration(modifiers);
			ret = fSpecialNonNull;
		}

		debug("<-- process_module_class_interface_body_item - " + 
				((ret != null)?SVDBItem.getName(ret):"NULL"));

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
		SVDBTypeInfo type;
		boolean is_variable = true;

		// TODO: need to modify this to be different for class and module/interface
		// scopes
		type = parsers().dataTypeParser().data_type(modifiers);
		
		if (type == null) {
			error("Failed to parse type");
		}

		// Not a variable declaration
		if (lexer().peekOperator()) {
			return false;
		}

		// Handle parameterization
		do {

			if (lexer().peekOperator(",")) {
				lexer().eatToken();
			}

			String inst_name_or_var = lexer().readIdOrKeyword();

			if (inst_name_or_var == null) {
				is_variable = false;
				break;
			}

			debug("inst name or var: " + inst_name_or_var);

			if (lexer().peekOperator("(")) {
				type = new SVDBTypeInfoUserDef(type.getName(), SVDBDataType.ModuleIfc);
				
				// it's a module
				debug("module instantiation - " + inst_name_or_var);
				lexer().skipPastMatch("(", ")");
				
				SVDBModIfcInstItem item = new SVDBModIfcInstItem(
						type, inst_name_or_var);
				setLocation(item);
				fScopeStack.peek().addItem(item);
			} else {
				int attr = 0;
				String bounds = null;

				SVDBVarDeclStmt item = new SVDBVarDeclStmt(type, 0);
				SVDBVarDeclItem vi = new SVDBVarDeclItem(inst_name_or_var);

				// non-module instance
				if (lexer().peekOperator("[")) {
					// Array type
					vi.setArrayDim(parsers().dataTypeParser().var_dim());
				}
				
				setLocation(item);
				setLocation(vi);
				item.addVar(vi);

				if (vi.getName() == null || vi.getName().equals("")) {
					System.out.println("    " +
							fFile.getFilePath() + ":"  + item.getLocation().getLine());
				}
				item.setAttr(attr);
				fScopeStack.peek().addItem(item);
			}

			if (lexer().peekOperator("=")) {
				lexer().eatToken();
				/*String expr = */parsers().exprParser().expression();
			}

		} while (lexer().peekOperator(","));

		fNewStatement = true;

		return is_variable;
	}

	public static boolean isFirstLevelScope(String id, int modifiers) {
		return ((id == null) ||
				id.equals("class") ||
				// virtual interface is a valid field
				(id.equals("interface") && (modifiers & SVDBFieldItem.FieldAttr_Virtual) == 0)
				|| id.equals("module"));
	}

	public static boolean isSecondLevelScope(String id) {
		return (id.equals("task") || id.equals("function")
				|| id.equals("always") || id.equals("initial")
				|| id.equals("assign") 
				|| id.equals("endtask") || id.equals("endfunction"));
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

	public void clrNewStatement() {
		fNewStatement = false;
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

	private static final String RecognizedOps[];
	
	static {
//		String misc[] = {":", "::", ":/", ":=", ".", "#", "'"};
		String misc[] = {"::", ":/", ":=", ".", "#", "'"};
		RecognizedOps = new String[SVLexer.RelationalOps.length + misc.length];
		
		int idx=0;
		for (String o : SVLexer.RelationalOps) {
			RecognizedOps[idx++] = o;
		}
		
		for (String o : misc) {
			RecognizedOps[idx++] = o;
		}
	}
	
	private static final String fPrefixOps[] = {
		"'", "^", "~", "-", "!", "|", "&", "++", "--"
	};
	
	private static final String fSuffixOps[] = {
		"++", "--"
	};
	
	public String readExpression(boolean accept_colon) throws SVParseException {
		lexer().startCapture();
		while (lexer().peek() != null) {
			debug("First Token: " + lexer().peek());
			if (lexer().peekOperator(fPrefixOps)) {
				while (lexer().peek() != null && lexer().peekOperator(fPrefixOps)) {
					lexer().eatToken();
				}
			}
			if (lexer().peekOperator("(")) {
				lexer().skipPastMatch("(", ")");
			} else if (lexer().peekOperator("{")) {
				lexer().skipPastMatch("{", "}");
			} else if (lexer().peekOperator("[")) {
				lexer().skipPastMatch("[", "]");
			} else if (lexer().peekOperator("-")) {
				lexer().eatToken();
				if (lexer().peekOperator("(")) {
					lexer().skipPastMatch("(", ")");
				} else {
					lexer().eatToken();
				}
			} else if (lexer().peekNumber()) {
				lexer().eatToken();
				// time unit
				if (lexer().peek().equals("fs") || lexer().peek().equals("ps") ||
						lexer().peek().equals("ns") || lexer().peek().equals("us") ||
						lexer().peek().equals("ms") || lexer().peek().equals("s")) {
					lexer().eatToken();
				}
			} else if (!lexer().peekOperator()) {
				lexer().eatToken();
				// See if this is a task/function call
				if (lexer().peekOperator("(")) {
					lexer().skipPastMatch("(", ")");
				} else if (lexer().peekOperator("[")) {
					// See if this is subscripting
					lexer().skipPastMatch("[", "]");
				}
			} else {
				debug("Escape 1: " + lexer().peek());
				break;
			}

			// Skip any subscripting
			while (lexer().peekOperator("[")) {
				lexer().skipPastMatch("[", "]");
			}
			
			debug("Second Token: " + lexer().peek());

			// Remove any suffix operators
			if (lexer().peekOperator(fSuffixOps)) {
				// Unary suffix operators, such as ++ and --
				lexer().eatToken();
			}
			
			if ((lexer().peekOperator(":") && accept_colon) || lexer().peekOperator(RecognizedOps)) {
				lexer().eatToken();
			} else if (lexer().peekOperator("(")) {
				lexer().skipPastMatch("(", ")");
			} else if (lexer().peekOperator("[")) {
				lexer().skipPastMatch("[", "]");
			} else if (lexer().peekKeyword("with")) {
				// randomize with
				lexer().eatToken();
				lexer().readOperator("{");
				lexer().skipPastMatch("{", "}");
			} else {
				debug("Escape 2: " + lexer().peek());
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
		debug(msg, null);
	}

	public void debug(String msg, Exception e) {
		if (e != null) {
			fLog.debug(msg, e);
		} else {
			fLog.debug(msg);
		}
	}
	
	public String delay3() throws SVParseException {
		lexer().readOperator("#");
		
		if (lexer().peekOperator("(")) {
			lexer().eatToken();
			/* min / base */ parsers().exprParser().expression();
			if (lexer().peekOperator(",")) {
				lexer().eatToken();
				/* typ */ parsers().exprParser().expression();

				lexer().readOperator(",");
				/* max */ parsers().exprParser().expression();
			}
			lexer().readOperator(")");
		} else {
			parsers().exprParser().expression();
		}
		
		return lexer().endCapture();
	}

	public void error(String msg, String filename, int lineno, int linepos) {
		SVDBMarkerItem marker = new SVDBMarkerItem(SVDBMarkerItem.MARKER_ERR,
				SVDBMarkerItem.KIND_GENERIC, msg);
		marker.setLocation(new SVDBLocation(lineno, linepos));

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

	// Leftover from pre-processor parser
	public void enter_package(String name) {}
	public void leave_package() {
	}

	public void leave_interface_decl() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Interface) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void leave_class_decl() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Class) {
//			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	private void leave_struct_decl(String name) {
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

	public void leave_module_decl() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Module) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void leave_program_decl() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Program) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	private void setStartLocation(SVDBItem item) {
		ScanLocation loc = getStartLocation();

		if (loc != null) {
			item.setLocation(new SVDBLocation(loc.getLineNo(), loc.getLinePos()));
		}
	}

	private void setLocation(ISVDBItemBase item) {
		ScanLocation loc = getStmtLocation();
		item.setLocation(new SVDBLocation(loc.getLineNo(), loc.getLinePos()));
	}

	private void setEndLocation(SVDBScopeItem item) {
		ScanLocation loc = getStmtLocation();
		item.setEndLocation(new SVDBLocation(loc.getLineNo(), loc.getLinePos()));
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

		
		error(e.getMessage(), e.getFilename(), e.getLineno(), e.getLinepos());
		
		// Send the full error forward
		fLog.debug("Parse Error: " + e.getMessage() + " " + 
				e.getFilename() + ":" + e.getLineno(), e);
		
		throw e;
	}
	
	public void error(String msg) throws SVParseException {
		error(SVParseException.createParseException(msg, 
				fFile.getFilePath(), getLocation().getLineNo(), getLocation().getLinePos()));
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
