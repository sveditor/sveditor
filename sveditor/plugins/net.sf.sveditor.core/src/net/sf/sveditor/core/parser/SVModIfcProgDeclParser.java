/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBFieldItem;
import net.sf.sveditor.core.db.SVDBInterfaceDecl;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.SVDBModuleDecl;
import net.sf.sveditor.core.db.SVDBProgramDecl;
import net.sf.sveditor.core.db.stmt.SVDBParamPortDecl;

public class SVModIfcProgDeclParser extends SVParserBase {
	
	public SVModIfcProgDeclParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(ISVDBAddChildItem parent, int qualifiers) throws SVParseException {
		String id;
		String module_type_name = null;
		SVDBModIfcDecl module = null;

		if (fDebugEn) {
			debug("--> process_mod_ifc_prog()");
		}
		
		long start = fLexer.getStartLocation();
		String type_name = fLexer.readKeyword("module", "macromodule",
				"interface", "program");
		SVDBItemType type = null;
		if (type_name.equals("module") || type_name.equals("macromodule")) {
			type = SVDBItemType.ModuleDecl;
		} else if (type_name.equals("interface")) {
			type = SVDBItemType.InterfaceDecl;
		} else if (type_name.equals("program")) {
			type = SVDBItemType.ProgramDecl;
		} else {
			error("Unsupported module/interface/program type-name " + type_name);
		}
		
		if (fLexer.peekKeyword("static", "automatic")) {
			// TODO: tag with lifetime
			fLexer.eatToken();
		}
		
		if (type == SVDBItemType.ProgramDecl && fLexer.peekOperator(OP.SEMICOLON)) {
			// anonymous program block
			module_type_name = "";
		} else {
			module_type_name = fLexer.readId();
		}

		switch (type) {
			case ModuleDecl:
				module = new SVDBModuleDecl(module_type_name);
				break;
			case InterfaceDecl:
				module = new SVDBInterfaceDecl(module_type_name);
				break;
			case ProgramDecl:
				module = new SVDBProgramDecl(module_type_name);
				break;
			default:
				break;
		}

		module.setLocation(start);
		
		parent.addChildItem(module);
		
		if (type != SVDBItemType.ProgramDecl) {
			// May have imports prior to the port declaration
			while (fLexer.peekKeyword("import")) {
				// Import statement
				parsers().impExpParser().parse_import(module);
			}
		}

		// Handle modules with parameters
		if (fLexer.peekOperator(OP.HASH)) {
			// Handle in-line parameter declarations
			module.getParameters().addAll(parsers().paramPortListParser().parse());
		}

		if (fLexer.peekOperator(OP.LPAREN)) {
			// port-list
			List<SVDBParamPortDecl> ports = parsers().portListParser().parse();
			for (SVDBParamPortDecl p : ports) {
				p.setParent(module);
			}
			module.getPorts().addAll(ports);
		}
		
		if (fLexer.peekKeyword("end" + type_name)) {
			fLexer.eatToken();
			if (fDebugEn) {
				debug("<-- process_mod_ifc_prog(early escape)");
			}
			
			return;
		}
		
		fLexer.readOperator(OP.SEMICOLON);
		
		// Extern module/programs don't have bodies
		if ((qualifiers & SVDBFieldItem.FieldAttr_Extern) == 0) {
			while (fLexer.peek() != null && !fLexer.peekKeyword("end" + type_name)) {
				try {
					fParsers.modIfcBodyItemParser().parse(module, type_name);
				} catch (SVParseException e) {
					// TODO: How to adapt?
					if (fDebugEn) {
						debug("Module body item parse failed", e);
					}
					while (fLexer.peek() != null && !fLexer.peekOperator(OP.SEMICOLON) &&
							!fLexer.peekKeyword("end"+ type_name)) {
						fLexer.eatToken();
					}
				}

				// TODO: Should have already been added ?
				// fScopeStack.peek().addItem(item);
			}
			
			long end = fLexer.getStartLocation();
			module.setEndLocation(end);
			fLexer.readKeyword("end" + type_name);
			
			// Optional labeled end
			if (fLexer.peekOperator(OP.COLON)) {
				fLexer.eatToken();
				fLexer.readId();
			}
		} else {
			long end = fLexer.getStartLocation();
			module.setEndLocation(end);
		}

		if (fDebugEn) {
			debug("<-- process_mod_ifc_prog()");
		}
	}

}
