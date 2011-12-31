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
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.SVDBPackageDecl;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
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
		ISVParser, ILogLevelListener {
	private SVScannerTextScanner fInput;
	private SVLexer fLexer;

	private boolean fNewStatement;
	private ScanLocation fStmtLocation;
	private ScanLocation fStartLocation;

	private IDefineProvider fDefineProvider;
	private boolean fEvalConditionals = true;

	private SVDBFile fFile;
	private Stack<SVDBScopeItem> fScopeStack;
	private SVParsers 					fSVParsers;
	private List<SVParseException> 		fParseErrors;
	private int							fParseErrorMax;
	private LogHandle					fLog;
	private boolean						fDebugEn;
	private List<SVDBMarker>			fMarkers;

	public ParserSVDBFileFactory(IDefineProvider dp) {
		// Setup logging
		fLog = LogFactory.getLogHandle(
				"ParserSVDBFileFactory", ILogHandle.LOG_CAT_PARSER);
		fLog.addLogLevelListener(this);
		logLevelChanged(fLog);
		
		setDefineProvider(dp);
		fScopeStack = new Stack<SVDBScopeItem>();

		if (dp != null) {
			setDefineProvider(dp);
		}
		
		fParseErrors = new ArrayList<SVParseException>();
		fParseErrorMax = 5;
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
		if (fMarkers != null) {
			SVDBMarker marker = new SVDBMarker(
					MarkerType.Error, MarkerKind.UndefinedMacro, msg);
			marker.setLocation(new SVDBLocation(lineno, 0));
			fMarkers.add(marker);
		}
	}

	/**
	 * 
	 * @param in
	 */
	private void scan(InputStream in, String filename, List<SVDBMarker> markers) {

		fNewStatement = true;
		fMarkers = markers;
		
		if (fMarkers == null) {
			fMarkers = new ArrayList<SVDBMarker>();
		}

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
		fSVParsers = new SVParsers();
		fSVParsers.init(this);

		try {
			process_file();
		} catch (SVParseException e) {
			if (fDebugEn) {
				debug("ParseException: post-process()", e);
			}
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
	
	private void top_level_item(ISVDBScopeItem parent) throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		int modifiers = scan_qualifiers(false);

		try {
			if (fLexer.peekOperator("(*")) {
				fSVParsers.attrParser().parse(parent);
			}
		} catch (SVParseException e) {
			// Ignore the error and allow another parser to deal with
		}
		
		if (fLexer.peekKeyword("bind")) {
			parsers().modIfcBodyItemParser().parse_bind(parent);
		} else if (fLexer.peekKeyword("class")) {
			parsers().classParser().parse(parent, modifiers);
			fNewStatement = true;
		} else if (fLexer.peekKeyword("module","macromodule","interface","program")) {
			// enter module scope
			parsers().modIfcProgParser().parse(parent, modifiers);
		} else if (fLexer.peekKeyword("package")) {
			package_decl(parent);
		} else if (fLexer.peekKeyword("import")) {
			parsers().impExpParser().parse_import(parent);
			fNewStatement = true;
		} else if (fLexer.peekKeyword("export")) {
			parsers().impExpParser().parse_export(parent);
			fNewStatement = true;
		} else if (fLexer.peekKeyword("typedef")) {
			parsers().dataTypeParser().typedef(parent);
			fNewStatement = true;
		} else if (fLexer.peekKeyword("function","task")) {
			parsers().taskFuncParser().parse(parent, start, modifiers);
			fNewStatement = true;
		} else if (fLexer.peekKeyword("constraint")) {
			parsers().constraintParser().parse(parent, modifiers);
		} else if (fLexer.peekKeyword("parameter","localparam")) {
			parsers().modIfcBodyItemParser().parse_parameter_decl(parent);
		} else if (fLexer.peekKeyword("timeprecision", "timeunit")) {
			parsers().modIfcBodyItemParser().parse_time_units_precision(parent);
		} else if (!fLexer.peekOperator()) {
			parsers().modIfcBodyItemParser().parse_var_decl_module_inst(parent, modifiers);
		} else if (fLexer.peekOperator(";")) {
			// null statement
			fLexer.eatToken();
		} else {
			// TODO: check for a data declaration
			error("Unknown top-level element \"" + fLexer.peek() + "\"");
		}
	}

	private void process_file() throws SVParseException {
		
		while (fLexer.peek() != null) {
			top_level_item(fFile);
		}
	}

	public int scan_qualifiers(boolean param)
			throws EOFException {
		int modifiers = 0;
		Map<String, Integer> qmap = (param) ? fTaskFuncParamQualifiers
				: fFieldQualifers;

		String id;
		while ((id = fLexer.peek()) != null && qmap.containsKey(id)) {
			if (fDebugEn) {
				debug("item modified by \"" + id + "\"");
			}
			modifiers |= qmap.get(id);

			fLexer.eatToken();
		}

		return modifiers;
	}

	public String scopedIdentifier(boolean allow_keywords) throws SVParseException {
		StringBuilder id = new StringBuilder();

		if (!allow_keywords) {
			id.append(fLexer.readId());
		} else if (fLexer.peekKeyword() || fLexer.peekId()) {
			id.append(fLexer.eatToken());
		} else {
			error("scopedIdentifier: starts with " + fLexer.peek());
		}

		while (fLexer.peekOperator("::")) {
			id.append("::");
			fLexer.eatToken();
			if (fLexer.peekKeyword("new") ||
					(allow_keywords && fLexer.peekKeyword())) {
				id.append(fLexer.readKeyword());
			} else {
				id.append(fLexer.readId());
			}
		}

		return id.toString();
	}

	public List<SVToken> scopedIdentifier_l(boolean allow_keywords) throws SVParseException {
		List<SVToken> ret = new ArrayList<SVToken>();

		if (!allow_keywords) {
			ret.add(fLexer.readIdTok());
		} else if (fLexer.peekKeyword() || fLexer.peekId()) {
			ret.add(fLexer.consumeToken());
		} else {
			error("scopedIdentifier: starts with " + fLexer.peek());
		}

		while (fLexer.peekOperator("::",".")) {
			ret.add(fLexer.consumeToken());
			if (fLexer.peekKeyword("new") ||
					(allow_keywords && fLexer.peekKeyword())) {
				ret.add(fLexer.consumeToken());
			} else {
				ret.add(fLexer.readIdTok());
			}
		}

		return ret;
	}

	public List<SVToken> scopedStaticIdentifier_l(boolean allow_keywords) throws SVParseException {
		List<SVToken> ret = new ArrayList<SVToken>();

		if (!allow_keywords) {
			ret.add(fLexer.readIdTok());
		} else if (fLexer.peekKeyword() || fLexer.peekId()) {
			ret.add(fLexer.consumeToken());
		} else {
			error("scopedIdentifier: starts with " + fLexer.peek());
		}
		
		while (fLexer.peekOperator("::")) {
			ret.add(fLexer.consumeToken());
			if (allow_keywords && fLexer.peekKeyword()) {
				ret.add(fLexer.consumeToken());
			} else {
				ret.add(fLexer.readIdTok());
			}
		}

		return ret;
	}

	/**
	 * Tries to read a scoped static identifier list
	 * 
	 * @param allow_keywords
	 * @return
	 * @throws SVParseException
	 */
	public List<SVToken> peekScopedStaticIdentifier_l(boolean allow_keywords) throws SVParseException {
		List<SVToken> ret = new ArrayList<SVToken>();

		if (!allow_keywords) {
			if (fLexer.peekId()) {
				ret.add(fLexer.readIdTok());
			} else {
				return ret;
			}
		} else if (fLexer.peekKeyword() || fLexer.peekId()) {
			ret.add(fLexer.consumeToken());
		} else {
			return ret;
		}

		while (fLexer.peekOperator("::")) {
			ret.add(fLexer.consumeToken());
			if (allow_keywords && fLexer.peekKeyword()) {
				ret.add(fLexer.consumeToken());
			} else {
				ret.add(fLexer.readIdTok());
			}
		}

		return ret;
	}

	public String scopedIdentifierList2Str(List<SVToken> scoped_id) {
		StringBuilder sb = new StringBuilder();
		for (SVToken tok : scoped_id) {
			sb.append(tok.getImage());
		}
		return sb.toString();
	}

	private void package_decl(ISVDBScopeItem parent) throws SVParseException {
		if (fLexer.peekOperator("(*")) {
			fSVParsers.attrParser().parse(parent);
		}
		SVDBPackageDecl pkg = new SVDBPackageDecl();
		pkg.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword("package");

		if (fLexer.peekKeyword("static","automatic")) {
			fLexer.eatToken();
		}

		String pkg_name = readQualifiedIdentifier();
		pkg.setName(pkg_name);
		fLexer.readOperator(";");
		
		parent.addChildItem(pkg);

		while (fLexer.peek() != null && !fLexer.peekKeyword("endpackage")) {
			top_level_item(pkg);
			
			if (fLexer.peekKeyword("endpackage")) {
				break;
			}
		}
		
		pkg.setEndLocation(fLexer.getStartLocation());
		fLexer.readKeyword("endpackage");
		// Handled named package end-block
		if (fLexer.peekOperator(":")) {
			fLexer.eatToken();
			fLexer.readId();
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
				SVDBParamPortDecl.FieldAttr_Virtual);
		fTaskFuncParamQualifiers.put("input",
				SVDBParamPortDecl.Direction_Input);
		fTaskFuncParamQualifiers.put("output",
				SVDBParamPortDecl.Direction_Output);
		fTaskFuncParamQualifiers.put("inout",
				SVDBParamPortDecl.Direction_Inout);
		fTaskFuncParamQualifiers.put("ref", SVDBParamPortDecl.Direction_Ref);
		fTaskFuncParamQualifiers.put("var", SVDBParamPortDecl.Direction_Var);
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

		fLexer.setNewlineAsOperator(true);
		// System.out.println("--> scan_statement() " + fLexer.peek() + "\n");

		while ((id = fLexer.peek()) != null) {
			/*
			System.out.println("scan_statement: id=\"" + id
					+ "\" ; NewStatement=" + fNewStatement);
			 */
			if (!fNewStatement && (id.equals(";") || id.equals("\n")
					|| (SVKeywords.isSVKeyword(id) && id.startsWith("end")))) {
				fNewStatement = true;
				fLexer.eatToken();
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
			fLexer.eatToken();
		}

		// System.out.println("<-- scan_statement() - " + id + "\n");
		fLexer.setNewlineAsOperator(false);
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
		if (!fLexer.peekId() && !fLexer.peekKeyword()) {
			return null;
		}
		StringBuffer ret = new StringBuffer();

		ret.append(fLexer.eatToken());

		while (fLexer.peekOperator("::")) {
			ret.append(fLexer.eatToken());
			ret.append(fLexer.eatToken());
		}
		/*
		while (fLexer.peekId() || fLexer.peekOperator("::") || fLexer.peekKeyword()) {
			ret.append(fLexer.eatToken());
		}
		 */

		return ret.toString();
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
	
	public ILogHandle getLogHandle() {
		return fLog;
	}
	
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = fLog.isEnabled();
	}
	
	public String strengths(int max_strengths		// maximum number of strengths that can be here
			) throws SVParseException {
		boolean done = false;
		int num_strengths = 0;
		while (done == false)  {
			if (fLexer.peekKeyword(SVKeywords.fStrength))  {
				// TODO: Read these until done ... don't know what we are going to do with them but anyway
				fLexer.readKeyword(SVKeywords.fStrength);
				num_strengths ++; 
			}
			if (fLexer.peekOperator(")"))  {
				fLexer.readOperator(")");
				done = true;
			}
			else  {
				// must be separated by comma's
				fLexer.readOperator(",");
			}
		}
		if (max_strengths < num_strengths)  {
			error("[Internal Error] Number of drive strengths '" + num_strengths + "' greater than maximum strengths '" + max_strengths + "' for this gate type");
		}
		return fLexer.endCapture();
	}
	public String delay_n(int max_delays) throws SVParseException {
		fLexer.readOperator("#");
		boolean has_min_max_typ = false;	    // is formatted as nnn:nnn:nnn
		boolean done_with_params = false;		// Done with delay params
		int num_delays= 0;						// Number of delay parameters
		
		
		if (fLexer.peekOperator("(")) {
			fLexer.eatToken();
			while (done_with_params == false)  {
				num_delays ++;
				// Can have up to max_delays delay operators
				// #(Delay_construct) - Normal delay
				// #(Rising_Delay_construct, Falling_Delay Construct) // Rising delay, falling delay
				// #(Rising_Delay_construct, Falling_Delay Construct, Decay_Delay_Construct) // Rising delay, falling delay
				// Where xxx_Delay_Construct is either:
				// <generic_delay>
				// <min_delay>:<typ_delay>:<max_delay>
				parsers().exprParser().expression();			// min or base
				if (fLexer.peekOperator(":")) {
					has_min_max_typ = true;	// is formatted as nnn:nnn:nnn
					fLexer.eatToken();
					/* typ */ parsers().exprParser().expression();
	
					fLexer.readOperator(":");
					/* max */ parsers().exprParser().expression();
				}
				if (fLexer.peekOperator(")"))  {
					fLexer.readOperator(")");
					done_with_params = true;
				}
				else if (fLexer.peekOperator(","))  {
					fLexer.readOperator(",");
					
				}
			}
		} else {
			parsers().exprParser().expression();
		}
		
		if (num_delays > max_delays)  {
			error("[Internal Error] Number of delay parameters '" + num_delays + "' greater than maximum delay parameters'" + max_delays + "' for this gate type");
		}
		return fLexer.endCapture();
	}

	public void error(String msg, String filename, int lineno, int linepos) {
		if (fMarkers != null) {
			SVDBMarker marker = new SVDBMarker(
					MarkerType.Error, MarkerKind.ParseError, msg);
			marker.setLocation(new SVDBLocation(lineno, linepos));
			fMarkers.add(marker);
		}
	}

	public SVDBFile parse(InputStream in, String name, List<SVDBMarker> markers) {
		fScopeStack.clear();
		
		fFile = new SVDBFile(name);
		fScopeStack.clear();
		fScopeStack.push(fFile);
		scan(in, name, markers);

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
		fSVParsers = new SVParsers();
		fSVParsers.init(this);
	}

	// Leftover from pre-processor parser
	public void enter_package(String name) {}
	public void leave_package() {
	}

	public void leave_interface_decl() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.InterfaceDecl) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void leave_class_decl() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.ClassDecl) {
//			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
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

	public void init(ISVScanner scanner) {}

	public void leave_module_decl() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.ModuleDecl) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
	}

	public void leave_program_decl() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.ProgramDecl) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
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

	public void enter_preproc_conditional(String type, String conditional) {}
	public void leave_preproc_conditional() {}
	public void comment(String comment) {}

	public void leave_covergroup() {
		if (fScopeStack.size() > 0
				&& fScopeStack.peek().getType() == SVDBItemType.Covergroup) {
			setEndLocation(fScopeStack.peek());
			fScopeStack.pop();
		}
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
		String msg = e.getMessage() + " " + 
				e.getFilename() + ":" + e.getLineno();
		if (fDebugEn) {
			fLog.debug("Parse Error: " + msg, e);
		}
		
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
