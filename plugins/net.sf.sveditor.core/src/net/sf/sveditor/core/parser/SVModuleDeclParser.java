package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBProgramBlock;
import net.sf.sveditor.core.scanner.SVClassIfcModParam;

public class SVModuleDeclParser extends SVParserBase {
	
	public SVModuleDeclParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBModIfcClassDecl parse() throws SVParseException {
		SVDBLocation start = lexer().getStartLocation();
		
		lexer().readKeyword("module");
		SVDBItem it = null;
		String id;
		List<SVClassIfcModParam> params = null;
		String super_name = null;
		List<SVClassIfcModParam> super_params = null;
		String module_type_name = null;
		String ports = null;
		SVDBModIfcClassDecl module = null;

		String type = lexer().eatToken();

		debug("--> process_module()");

		// TODO: Should remove this later
		parsers().SVParser().enter_scope("module", module);


		//
		// Skip up to point of module type name
		//

		if (lexer().peekId()) {
			module_type_name = lexer().readId();
		} else {
			return module; // TODO: ?
		}

		// Handle modules with parameters
		if (lexer().peekOperator("#")) {
			if (lexer().peekOperator("(")) {
				lexer().startCapture();
				lexer().skipPastMatch("(", ")");
				String p_str = lexer().endCapture();

				params = parsers().SVParser().parse_parameter_str(p_str);
			}
		}

		if (params == null) {
			params = new ArrayList<SVClassIfcModParam>();
		}

		// Module port-list
		if (lexer().peekOperator("(")) {
			lexer().startCapture();
			lexer().skipPastMatch("(", ")");
			ports = lexer().endCapture();
		}

		/* TODO:
		module = new SVDBModIfcClassDecl(module_type_name,
				SVDBItemType.Module);
		fScopeStack.peek().addItem(cls);
		fScopeStack.push(cls);

		setLocation(module);
		 */
		
		/*
		} else if (type.equals("program")) {
			SVDBProgramBlock p = new SVDBProgramBlock(module_type_name);

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
		}
		 */

		while ((id = parsers().SVParser().scan_statement()) != null) {
			debug("id=" + id);
			if (id.equals("end" + type)) {
				break;
			}
			SVDBItem item = parsers().SVParser().process_module_class_interface_body_item(type);

			// Check whether we aborted parsing the body because
			// we found a 1st-level scope keyword
			if (item == null) {
				break;
			}

			// TODO: Should have already been added ?
			// fScopeStack.peek().addItem(item);
		}

		// Pop the first-level scope
		parsers().SVParser().handle_leave_scope();

		debug("<-- process_module()");
		return module;
	}

}
