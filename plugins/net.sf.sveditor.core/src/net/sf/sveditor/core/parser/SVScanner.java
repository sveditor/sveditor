package net.sf.sveditor.core.parser;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import net.sf.sveditor.core.StringInputStream;

/**
 * 
 * @author ballance
 *
 * * Handle types with form <name>::<name>
 * - Module instances
 * * Handle non-single-word types: unsigned int/int unsigned
 * * Display bit sizes on variables: bit [4:0]
 * - Add covergroup as second-level scope
 * * Handle qualifiers (virtual) on classes
 * - Templates for class members
 */
public class SVScanner implements ISVScanner {
	private Stack<String>			fScopeStack = new Stack<String>();
	private Stack<SVScannerInput>	fInputStack = new Stack<SVScannerInput>();
	private Stack<Boolean>			fPreProcEn  = new Stack<Boolean>();
	
	private boolean					fNewStatement;
	private ScanLocation			fStmtLocation;
	
	private ISVScannerObserver		fObserver;
	private IDefineProvider			fDefineProvider;
	
	public SVScanner() {
		
	}
	
	public void setDefineProvider(IDefineProvider p) {
		fDefineProvider = p;
	}
	
	public ScanLocation getStmtLocation() {
		return fStmtLocation;
	}
	
	public void setObserver(ISVScannerObserver observer) {
		fObserver = observer;
	}

	/**
	 * 
	 * @param in
	 */
	public void scan(InputStream in, String filename) {
	
		fNewStatement = true;
		fInputStack.clear();
		fInputStack.push(new SVScannerInput(filename, in));
		
		fPreProcEn.clear();
		fPreProcEn.push(true);
		
		if (fObserver != null) {
			fObserver.enter_file(filename);
		}

		process();

		if (fObserver != null) {
			fObserver.leave_file();
		}
	}
	
	private void process() {
		String id;
		
		try {
			while ((id = scan_statement()) != null) {
				Pair<String, Integer> ret = scan_qualifiers(id, false);
				id = ret.fField1;
				
				if (id.equals("module") ||
						id.equals("interface") ||
						id.equals("class")) {
					// enter module scope
					process_interface_module_class(id);
				} else if (id.equals("package") || id.equals("endpackage")) {
					process_package(id);
				} else if (id.equals("import")) {
					process_import();
				}
			}
		} catch (EOFException e) {
		}
	}
	
	private void handle_preproc_directive(String type) throws EOFException {
		int ch = -1;
		
		System.out.println("preproc directive=" + type);
		
		if (type.equals("ifdef") || type.equals("ifndef")) {
			StringBuffer sb = new StringBuffer();
			int last_ch = -1;
			
			// TODO: use map
			ch = skipWhite(next_ch());
			
			while (true) {
				ch = next_ch();
				if (ch == '\n' && last_ch != '\\') {
					break;
				}
				if (ch != '\r') {
					last_ch = ch;
					sb.append((char)ch);
				}
				
				if (ch == '\n' && last_ch == '\\') {
					sb.setLength(sb.length()-2);
				}
			}
			fNewStatement = true;
			
			if (type.equals("ifdef")) {
				fPreProcEn.push(false);
			} else {
				fPreProcEn.push(true);
			}
		} else if (type.equals("else")) {
			if (fPreProcEn.size() > 0) {
				boolean en = fPreProcEn.pop();
				fPreProcEn.push(!en);
			}
		} else if (type.equals("endif")) {
			if (fPreProcEn.size() > 0) {
				fPreProcEn.pop();
			}
		} else if (type.equals("define")) {
			List<String> params = new ArrayList<String>();
			
			ch = skipWhite(get_ch());
			StringBuffer def_line_i = new StringBuffer();
			def_line_i.append(readLine(ch));
			
			for (int i=0; i<def_line_i.length(); i++) {
				if (def_line_i.charAt(i) == '\n' && i+1 < def_line_i.length()) {
					def_line_i.insert(i, '\\');
					i++;
				}
			}
			
			String def_line = def_line_i.toString();
			
			System.out.println("def_line=" + def_line);
			
			SVScannerInput in = new SVScannerInput("foo",
					new StringInputStream(def_line));
			
			String def_id = null;
			String define = "";
			
			try {
				int ch2 = in.skipWhite(in.get_ch());
				
				def_id = in.readIdentifier(ch2);
				
				ch2 = in.skipWhite(in.get_ch());

				if (ch2 == '(') {
					// macro parameters
					ch2 = in.skipPastMatch("()");
					ch2 = in.skipWhite(ch2);
				}
				
				define = in.readLine(ch2);

			} catch (EOFException e) { }
			
			if (fObserver != null) {
				System.out.println("def_id=" + def_id + " define=" + define);
				fObserver.preproc_define(def_id, params, define);
			}
		} else if (type.equals("include")) {
			ch = get_ch();
			
			while (Character.isWhitespace(ch)) {
				ch = get_ch();
			}

			System.out.println("post-include ch=" + (char)ch);
			
			if (ch == '"') {
				String inc = readString(ch);
				
				System.out.println("inc=" + inc);
				if (fObserver != null) {
					fObserver.preproc_include(inc);
				}
			}
		} else {
			List<String> params = new ArrayList<String>();
			// macro expansion
			ch = skipWhite(next_ch());
			
			// TODO: get params
			if (ch == '(') {
				ch = skipPastMatch("()");
			}
			
			String val = "";
			
			if (fDefineProvider != null) {
				val = fDefineProvider.getDefineVal(type, params);
			}
			
			System.out.println("def value: \"" + val + "\"");

			if (val != null) {
				fInputStack.peek().pushUnaccContent(val);
			}
		}
	}
	
	private void process_initial_always(String id) throws EOFException {
		int ch = skipWhite(get_ch());
		
		if (id.equals("always")) {
			if (ch == '@') {
				ch = skipWhite(next_ch());
			}
			
			if (ch == '(') {
				ch = skipPastMatch("()");
			}
		}
		
		ch = skipWhite(ch);
		
		id = readIdentifier(ch);
		
		if (id == null) {
			System.out.println("ch=" + (char)ch);
		}
		
		if (id != null && id.equals("begin")) {
			int begin_cnt = 1;
			int end_cnt = 0;
			
			do {
				do {
					ch = skipWhite(next_ch());
				} while (ch != -1 && !Character.isJavaIdentifierStart(ch));
				
				id = readIdentifier(ch);
				
				if (id.equals("begin")) {
					begin_cnt++;
				} else if (id.equals("end")) {
					end_cnt++;
				}
			} while (id != null && begin_cnt != end_cnt);
		} else {
			// single-statement begin.
		}
	}
	
	private void process_constraint(String id) throws EOFException {
		int ch = get_ch();
		
		ch = skipWhite(ch);
		
		String cname = readIdentifier(ch);
		
		ch = skipWhite(ch);
		
		if (ch == '{') {
			ch = skipPastMatch("{}");
		}
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
		modifiers = mod_ret.fField2;

		
		if (id.equals("function")) {
			// could have a return type.
			unget_ch(ch);
			unget_str(tf_name + " ");
			ch = skipWhite(next_ch());
			String typename = readTypeName(ch, false);
			ch = skipWhite(next_ch());
			
			if (ch == '(' || ch == ';') {
				// no return type
				tf_name = typename;
			} else {
				tf_name = readIdentifier(ch);
				ch = skipWhite(get_ch());
			}
		}
		
		debug("post-task \"" + tf_name + "\" ch=" + (char)ch);
		
		if (ch == '(') {
			
			String t, n;
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
					t += endCapture();
					ch = skipWhite(ch);
				}
				
				SVTaskFuncParam p = new SVTaskFuncParam(t, n);
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
			fObserver.enter_task_decl(tf_name, modifiers, params);
		}
		
		debug("" + id + " " + tf_name);
		
		String exp_end = "end" + id;
		while ((id = scan_statement()) != null) {
			//
			if (id.equals(exp_end)) {
				break;
			} else if (isSecondLevelScope(id)) {
				if (fObserver != null) {
					fObserver.error("missing \"" + exp_end + "\"");
				}
				
				// 
				fNewStatement = true;
				unget_str(id + " ");
				break;
			} else if (isFirstLevelScope(id)) {
				if (fObserver != null) {
					fObserver.error("missing \"" + exp_end + "\"");
				}
				
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
		
		handle_leave_scope();
		
		return ret;
	}
	
	private boolean process_property(int modifiers, String id) throws EOFException {
		boolean ret = true;
		
		String stmt = null;
		do {
			stmt = scan_statement();
		} while (stmt != null && stmt.equals("endproperty"));
		
		return ret;
	}
	
	private void process_interface_module_class(String type) throws EOFException {
		String id;
		List<SVClassIfcModParam>	params = null; 
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

		// Module port-list
		ch = skipWhite(ch);
		if (ch == '(') {
			startCapture(ch);
			ch = skipPastMatch("()");
			ports = endCapture();
		}
		ch = skipWhite(ch);
		
		if (fObserver != null) {
			if (type.equals("module")) {
				fObserver.enter_module_decl(module_type_name, ports);
			} else if (type.equals("interface")) {
				fObserver.enter_interface_decl(module_type_name, ports);
			} else if (type.equals("class")) {
				fObserver.enter_class_decl(module_type_name, params);
			}
		}

		while ((id = scan_statement()) != null) {
			boolean ret;
			debug("id=" + id);
			if (id.equals("end" + type)) {
				break;
			}
			ret = process_module_class_interface_body_item(id);

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
	
	private void process_package(String id) throws EOFException {
		System.out.println("TODO: package => " + id);
	}
	
	private void handle_leave_scope() {
		handle_leave_scope(1);
	}
	
	private void handle_leave_scope(int levels) {
		for (int i=0; i<levels; i++) {
			String type = fScopeStack.pop();
			
			if (fObserver != null) {
				if (type.equals("module")) {
					fObserver.leave_module_decl();
				} else if (type.equals("interface")) {
					fObserver.leave_interface_decl();
				} else if (type.equals("class")) {
					fObserver.leave_class_decl();
				} else if (type.equals("task") || type.equals("function")) {
					fObserver.leave_task_decl();
				}
			}
		}
	}
	
	private List<SVClassIfcModParam> parse_parameter_str(String p_str) {
		List<SVClassIfcModParam> ret = new ArrayList<SVClassIfcModParam>();
		SVScannerInput in = new SVScannerInput("p", new StringInputStream(p_str));
		int    ch = 0;
		String id;
		
		try {
			
			ch = in.skipWhite(in.next_ch());
			if (ch != '(') {
				in.unget_ch(ch);
			}
			
			while (ch != -1) {
				ch = in.skipWhite(in.next_ch());

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

				ch = in.skipWhite(in.next_ch());

				if (ch == '(') {
					ch = in.skipPastMatch("()");
				}

				ch = in.skipWhite(ch);

				ch = in.skipToChar(ch, ',');

			}
		} catch (EOFException e) {
			// Ignore, since this just means we hit the end of the string
		}
		
		return ret;
	}
	
	private void process_import() throws EOFException {
		int ch = skipWhite(next_ch());
		
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
		
		fTaskFuncParamQualifiers = new HashMap<String, Integer>();
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
	
	private boolean process_module_class_interface_body_item(String id) throws EOFException {
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
		
		debug("body item is: " + id);

		if (id.equals("task") || id.equals("function")) {
			unget_ch(ch);
			ret = process_task_function(modifiers, id);
		} else if (id.equals("property")) {
			ret = process_property(modifiers, id);
		} else if (id.equals("always") || id.equals("initial")) {
			unget_ch(ch);
			process_initial_always(id);
		} else if (id.equals("constraint")) {
			unget_ch(ch);
			process_constraint(id);
		} else if (id.startsWith("end")) {
			// it's likely that we've encountered a parse error 
			// or incomplete text section.
			if (fScopeStack.size() > 0) {
				// We've hit end of our current section
				if (("end" + fScopeStack.peek()).equals(id)) {
					fScopeStack.pop();
				}
			}
		} else if (isFirstLevelScope(id)) {
			// We've hit a first-level qualifier. This probably means that
			// there is a missing
			unget_str(id + " ");
			fNewStatement = true;
			ret = false; 
		} else {
			// likely a variable or module declaration
			List<String> vars = new ArrayList<String>();
			
			debug("Likely VarDecl: " + id);
			
			unget_ch(ch);
			unget_str(id + " ");
			ch = skipWhite(next_ch());
			
			id = readTypeName(ch, false);
			ch = skipWhite(get_ch());
			
			// First, skip qualifiers
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
			
			// Handle parameterization
			do {
				
				if (ch == ',') {
					ch = next_ch();
				}
				
				ch = skipWhite(ch);
			
				String inst_name_or_var = readIdentifier(ch);
				debug("inst name or var: " + inst_name_or_var);
				
				ch = skipWhite(get_ch());
				
				if (ch == '(') {
					// it's a module
					debug("module instantation");
					ch = skipPastMatch("()");
					
					if (ch == ';') {
						unget_ch(ch);
					}
					break;
				} else {
					vars.add(inst_name_or_var);
				}

				ch = skipWhite(ch);
			} while (ch == ',');
			
			if (fObserver != null) {
				fObserver.variable_decl(id, modifiers, vars);
			}
		}
		
		debug("<-- process_module_class_interface_body_item");
		
		return ret;
	}
	
	private boolean isFirstLevelScope(String id) {
		return (id.equals("class") || 
				id.equals("interface") ||
				id.equals("module"));
	}
	
	private boolean isSecondLevelScope(String id) {
		return (id.equals("task") ||
				id.equals("function"));
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
					break;
					
				// Ignore whitespace...
				case ' ':
				case '\t':
					break;
					
				default:
					if (fNewStatement) {
						String id = null;
						fStmtLocation = getLocation();
						if (Character.isJavaIdentifierStart(ch)) {
							id = readIdentifier(ch);
							
							if (id != null) {
								fNewStatement = false;
							}
							
							if (fPreProcEn.peek()) {
								return id;
							}
						} else if (ch == '`') {
							ch = skipWhite(next_ch());
							handle_preproc_directive(readIdentifier(ch));
							
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
		if (fInputStack.size() > 0) {
			return fInputStack.peek().readIdentifier(ci);
		} else {
			return "";
		}
	}

	private String readLine(int ci) throws EOFException {
		if (fInputStack.size() > 0) {
			return fInputStack.peek().readLine(ci);
		} else {
			return "";
		}
	}
	
	private String readString(int ci) throws EOFException {
		if (fInputStack.size() > 0) {
			return fInputStack.peek().readString(ci);
		} else {
			return "";
		}
	}

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
	
	private boolean isBuiltInType(String id) {
		return (id.equals("int") || id.equals("integer") || 
				id.equals("unsigned") || id.equals("signed") ||
				id.equals("bit") || id.equals("void"));
	}
	
	private String readTypeName(int ch, boolean task_func) throws EOFException {
		StringBuffer ret = new StringBuffer();
		String id = null;
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
				
				ret.append(" ");
				ret.append(bitrange);
				ret.append(" ");
				is_builtin |= (1 << idx);
				ch = skipWhite(ch);
			}
			
			if (!Character.isJavaIdentifierStart(ch)) {
				unget_ch(ch);
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
							
							List<SVClassIfcModParam> p = parse_parameter_str(templ);
							
							// TODO: add template info
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
				
				ret.append(" ");
				ret.append(bitrange);
				ret.append(" ");
				ch = skipWhite(ch);
			}
			
			idx++;
		}
		
		if (ch != -1) {
			unget_ch(ch);
		}
		
		debug("--> readTypeName(task_func=" + task_func + ") -> " + 
				ret.toString().trim());
		if (ret.length() != 0) {
			return ret.toString().trim();
		} else {
			return null;
		}
	}
	
	private int skipWhite(int ch) throws EOFException {
		if (fInputStack.size() > 0) {
			return fInputStack.peek().skipWhite(ch);
		} else {
			return -1;
		}
	}

	private void startCapture(int ch) {
		if (fInputStack.size() > 0) {
			fInputStack.peek().startCapture(ch);
		}
	}

	private void startCapture() {
		startCapture(-1);
	}
	
	private String endCapture() throws EOFException {
		if (fInputStack.size() > 0) {
			return fInputStack.peek().endCapture();
		} else {
			return "";
		}
	}

	private int skipPastMatch(String pair) throws EOFException {
		if (fInputStack.size() > 0) {
			return fInputStack.peek().skipPastMatch(pair);
		} else {
			return -1;
		}
	}

	private int skipPastMatch(String pair, String escape) throws EOFException {
		if (fInputStack.size() > 0) {
			return fInputStack.peek().skipPastMatch(pair, escape);
		} else {
			return -1;
		}
	}

	/**
	 * next_ch()
	 * 
	 * Returns the next character, after skipping any comments
	 * 
	 * @return
	 */
	private int next_ch() throws EOFException {
		return fInputStack.peek().next_ch();
	}

	private int get_ch() throws EOFException {
		return get_ch(true);
	}
	
	private void unget_str(String str) {
		if (fInputStack.size() > 0) {
			fInputStack.peek().unget_str(str);
		}
	}
	
	/*
	 * low-level character-retrieval. 
	 */
	private int get_ch(boolean eof_ex) throws EOFException {
		int ch = -1;
		
		while (fInputStack.size() > 0 && 
				(ch = fInputStack.peek().get_ch()) == -1) {
		}
		
		if (eof_ex && ch == -1) {
			throw new EOFException();
		}
		
		return ch;
	}
	
	private void unget_ch(int ch) {
		if (fInputStack.size() > 0) {
			fInputStack.peek().unget_ch(ch);
		}
	}
	
	public ScanLocation getLocation() {
		if (fInputStack.size() > 0) {
			return fInputStack.peek().getLocation();
		} else {
			return new ScanLocation("", 0, 0);
		}
	}

	private void debug(String msg) {
//		System.out.println(msg);
	}
	
}
