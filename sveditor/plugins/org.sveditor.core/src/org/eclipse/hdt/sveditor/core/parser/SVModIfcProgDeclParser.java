/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.parser;

import java.util.List;

import org.eclipse.hdt.sveditor.core.db.ISVDBAddChildItem;
import org.eclipse.hdt.sveditor.core.db.SVDBFieldItem;
import org.eclipse.hdt.sveditor.core.db.SVDBInterfaceDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBModuleDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBProgramDecl;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBParamPortDecl;

public class SVModIfcProgDeclParser extends SVParserBase {
	
	public SVModIfcProgDeclParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(ISVDBAddChildItem parent, int qualifiers) throws SVParseException {
		String module_type_name = null;
		SVDBModIfcDecl module = null;

		if (fDebugEn) {
			debug("--> process_mod_ifc_prog()");
		}
		
		long start = fLexer.getStartLocation();
		KW type_name = fLexer.readKeyword(KW.MODULE, KW.MACROMODULE, KW.INTERFACE, KW.PROGRAM);
		KW end_type = null;
		SVDBItemType type = null;
		
		switch (type_name) {
			case MODULE:
			case MACROMODULE:
				type = SVDBItemType.ModuleDecl;
				end_type = KW.ENDMODULE;
				break;
				
			case INTERFACE:
				type = SVDBItemType.InterfaceDecl;
				end_type = KW.ENDINTERFACE;
				break;
				
			case PROGRAM:
				type = SVDBItemType.ProgramDecl;
				end_type = KW.ENDPROGRAM;
				break;
			default:
				break;
		}
		
		if (fLexer.peekKeyword(KW.STATIC, KW.AUTOMATIC)) {
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
			while (fLexer.peekKeyword(KW.IMPORT)) {
				// Import statement
				parsers().impExpParser().parse_import(module);
			}
		}

		// Handle modules with parameters
		if (fLexer.peekOperator(OP.HASH)) {
			// Handle in-line parameter declarations
			module.addParameters(parsers().paramPortListParser().parse());
		}

		if (fLexer.peekOperator(OP.LPAREN)) {
			// port-list
			List<SVDBParamPortDecl> ports = parsers().portListParser().parse();
			for (SVDBParamPortDecl p : ports) {
				p.setParent(module);
			}
			module.getPorts().addAll(ports);
		}
		
		
		if (fLexer.peekKeyword(end_type)) {
			fLexer.eatToken();
			if (fDebugEn) {
				debug("<-- process_mod_ifc_prog(early escape)");
			}
			
			enter_type_scope(module);
			leave_type_scope(module);
			return;
		}
		
		fLexer.readOperator(OP.SEMICOLON);
		
		enter_type_scope(module);
		
		// Extern module/programs don't have bodies
		if ((qualifiers & SVDBFieldItem.FieldAttr_Extern) == 0) {
			while (fLexer.peek() != null && !fLexer.peekKeyword(end_type)) {
				try {
					fParsers.modIfcBodyItemParser().parse(module);
				} catch (SVParseException e) {
					// TODO: How to adapt?
					if (fDebugEn) {
						debug("Module body item parse failed", e);
					}
					while (fLexer.peek() != null && !fLexer.peekOperator(OP.SEMICOLON) &&
							!fLexer.peekKeyword(end_type)) {
						fLexer.eatToken();
					}
				}

				// TODO: Should have already been added ?
				// fScopeStack.peek().addItem(item);
			}
			
			long end = fLexer.getStartLocation();
			module.setEndLocation(end);
			fLexer.readKeyword(end_type);
			
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
		
		leave_type_scope(module);
	}

}
