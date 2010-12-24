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

import java.util.List;

import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBParamPort;

public class SVModIfcProgDeclParser extends SVParserBase {
	
	public SVModIfcProgDeclParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBModIfcClassDecl parse(int qualifiers) throws SVParseException {
		String id;
		String module_type_name = null;
		SVDBModIfcClassDecl module = null;

		debug("--> process_mod_ifc_prog()");
		
		SVDBLocation start = lexer().getStartLocation();
		String type_name = lexer().readKeyword("module", "macromodule",
				"interface", "program");
		SVDBItemType type = null;
		if (type_name.equals("module") || type_name.equals("macromodule")) {
			type = SVDBItemType.Module;
		} else if (type_name.equals("interface")) {
			type = SVDBItemType.Interface;
		} else if (type_name.equals("program")) {
			type = SVDBItemType.Program;
		} else {
			error("Unsupported module/interface/program type-name " + type_name);
		}
		
		if (lexer().peekKeyword("static", "automatic")) {
			// TODO: tag with lifetime
			lexer().eatToken();
		}
		
		if (type == SVDBItemType.Program && lexer().peekOperator(";")) {
			// anonymous program block
			module_type_name = "";
		} else {
			module_type_name = lexer().readId();
		}
		

		module = new SVDBModIfcClassDecl(module_type_name, type);
		module.setLocation(start);
		
		// TODO: Should remove this later
		parsers().SVParser().enter_scope(type_name, module);

		if (type != SVDBItemType.Program) {
			// May have imports prior to the port declaration
			while (lexer().peekKeyword("import")) {
				// Import statement
				parsers().SVParser().process_import();
			}
		}

		// Handle modules with parameters
		if (lexer().peekOperator("#")) {
			// Handle in-line parameter declarations
			module.getParameters().addAll(parsers().paramPortListParser().parse());
		}

		if (lexer().peekOperator("(")) {
			// port-list
			List<SVDBParamPort> ports = parsers().portListParser().parse();
			module.getPorts().addAll(ports);
		}
		lexer().readOperator(";");
		
		// TODO: should be cleaned up
		parsers().SVParser().setNewStatement();

		// Extern module/programs don't have bodies
		if ((qualifiers & SVDBFieldItem.FieldAttr_Extern) == 0) {
			while ((id = parsers().SVParser().scan_statement()) != null) {
				debug("id=" + id);
				if (id.equals("end" + type_name)) {
					break;
				}
				try {
					SVDBItem item = parsers().SVParser().process_module_class_interface_body_item(type_name);

					// Check whether we aborted parsing the body because
					// we found a 1st-level scope keyword
					if (item == null) {
						break;
					}
				} catch (SVParseException e) {
					// TODO: How to adapt?
					e.printStackTrace();
				}

				// TODO: Should have already been added ?
				// fScopeStack.peek().addItem(item);
			}
		}
		
		SVDBLocation end = lexer().getStartLocation();
		module.setEndLocation(end);
		lexer().readKeyword("end" + type_name);

		// Pop the first-level scope
		parsers().SVParser().handle_leave_scope();

		debug("<-- process_mod_ifc_prog()");
		return module;
	}

}
