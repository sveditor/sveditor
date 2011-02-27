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

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBTypeInfoClassType;

public class SVClassDeclParser extends SVParserBase {
	
	public SVClassDeclParser(ISVParser parser) {
		super(parser);
	}
	
	/**
	 * 
	 * [ virtual ] class [ lifetime ] class_identifier [ parameter_port_list ]
	 * [ extends class_type [ ( list_of_arguments ) ] ];
	 * @param qualifiers
	 * @return
	 * @throws SVParseException
	 */
	public SVDBClassDecl parse(int qualifiers) throws SVParseException {
		SVDBClassDecl cls = null;
		SVDBTypeInfoClassType cls_type;
		String id;
		String cls_type_name = null;
		
		debug("--> process_class()");
		
		// Expect to enter on 'class'
		lexer().readKeyword("class");
		SVDBLocation start_loc = lexer().getStartLocation();
		
		if (lexer().peekKeyword("automatic", "static")) {
			// TODO: set lifetime on class declaration
			lexer().eatToken();
		}

		//
		// Class ID
		//
		cls_type_name = parsers().SVParser().scopedIdentifier(
				((qualifiers & IFieldItemAttr.FieldAttr_SvBuiltin) != 0));
		
		cls = new SVDBClassDecl(cls_type_name);
		cls.setLocation(start_loc);
		
		cls_type = new SVDBTypeInfoClassType(cls_type_name);
		cls.setClassType(cls_type);
		
		// TODO: Should remove this later
		parsers().SVParser().enter_scope("class", cls);
		
		if (lexer().peekOperator("#")) {
			// Handle classes with parameters
			cls.addParameters(parsers().paramPortListParser().parse());
		}
		
		if (lexer().peekKeyword("extends")) {
			lexer().eatToken();
			cls.setSuperClass(parsers().dataTypeParser().class_type());

			if (lexer().peekOperator("#")) {
				// scanner().unget_ch('#');
				// TODO: List<SVDBModIfcClassParam> params = fParamDeclParser.parse();
				// cls.getSuperParameters().addAll(params);
				lexer().eatToken();
				if (lexer().peekOperator("(")) {
					lexer().skipPastMatch("(", ")");
				} else {
					lexer().eatToken();
				}
			}
		}
		
		lexer().readOperator(";");
		
		// Force new-statement
		parsers().SVParser().setNewStatement();
		
		// TODO: need a better system here...
		while ((id = parsers().SVParser().scan_statement()) != null) {
			ISVDBItemBase item;
			if (id.equals("endclass")) {
				break;
			}
			
			try {
				item = parsers().SVParser().process_module_class_interface_body_item("class");

				// Check whether we aborted parsing the body because
				// we found a 1st-level scope keyword
				if (item == null) {
					break;
				}
			} catch (SVParseException e) {
				// Catch error
			}
			
			// TODO: normally we'd add this item to the class, but that's already being done
		}

		cls.setEndLocation(lexer().getStartLocation());
		lexer().readKeyword("endclass");

		// endclass : classname
		if (lexer().peekOperator(":")) { 
			lexer().eatToken();
			lexer().readId();
		}
		
		// TODO: remove this later
		parsers().SVParser().handle_leave_scope();
		
		return cls;
	}

}
