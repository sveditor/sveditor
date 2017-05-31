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

import net.sf.sveditor.core.db.IFieldItemAttr;
import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBTypeInfoClassType;

public class SVClassDeclParser extends SVParserBase {
	
	public SVClassDeclParser(ISVParser parser) {
		super(parser);
	}
	
	/**
	 * 
	 * [ virtual|interface ] class [ lifetime ] class_identifier [ parameter_port_list ]
	 * [ extends class_type [ ( list_of_arguments ) ] ];
	 * @param qualifiers
	 * @return
	 * @throws SVParseException
	 */
	public void parse(ISVDBAddChildItem parent, int qualifiers) throws SVParseException {
		SVDBClassDecl cls = null;
		SVDBTypeInfoClassType cls_type;
		String cls_type_name = null;
		
		if (fDebugEn) {
			debug("--> process_class()");
		}
		
		// Expect to enter on 'class'
		long start_loc = fLexer.getStartLocation();
		fLexer.readKeyword(KW.CLASS);
		
		if (fLexer.peekKeyword(KW.AUTOMATIC, KW.STATIC)) {
			// TODO: set lifetime on class declaration
			fLexer.eatToken();
		}

		//
		// Class ID
		//
		cls_type_name = parsers().SVParser().scopedIdentifier(
				((qualifiers & IFieldItemAttr.FieldAttr_SvBuiltin) != 0));
		
		if (fDebugEn) {
			debug("  -- CLASS " + cls_type_name);
		}
		
		cls = new SVDBClassDecl(cls_type_name);
		cls.setLocation(start_loc);
		
		cls_type = new SVDBTypeInfoClassType(cls_type_name);
		cls.setClassType(cls_type);
		
		if (fLexer.peekOperator(OP.HASH)) {
			// Handle classes with parameters
			cls.addParameters(parsers().paramPortListParser().parse());
		}
		
		if (fLexer.peekKeyword(KW.EXTENDS)) {
			fLexer.eatToken();
			cls.setSuperClass(parsers().dataTypeParser().class_type());

			// class_type() should handle parameterized classes
			// TODO: what's this?
//			if (fLexer.peekOperator(OP.HASH, OP.LPAREN)) {
//				// scanner().unget_ch('#');
//				// TODO: List<SVDBModIfcClassParam> params = fParamDeclParser.parse();
//				// cls.getSuperParameters().addAll(params);
//				if (fLexer.peekOperator(OP.HASH)) {
//					fLexer.eatToken();
//				}
//				if (fLexer.peekOperator(OP.LPAREN)) {
//					fLexer.skipPastMatch("(", ")");
//				} else {
//					fLexer.eatToken();
//				}
//			}
		}
		
		fLexer.readOperator(OP.SEMICOLON);
		
		parent.addChildItem(cls);
		
		// TODO: need a better system here...
		while (fLexer.peek() != null && !fLexer.peekKeyword(KW.ENDCLASS)) {
			
			try {
				fParsers.modIfcBodyItemParser().parse(cls);
			} catch (SVParseException e) {
				// Catch error
				// TODO: recover from errors
				while (fLexer.peek() != null && 
						!fLexer.peekOperator(OP.SEMICOLON) && !fLexer.peekKeyword(KW.ENDCLASS)) {
					fLexer.eatToken();
				}
			}
		}

		cls.setEndLocation(fLexer.getStartLocation());
		fLexer.readKeyword(KW.ENDCLASS);

		// endclass : classname
		if (fLexer.peekOperator(OP.COLON)) { 
			fLexer.eatToken();
			fLexer.readId();
		}
		
		if (fDebugEn) {
			debug("<-- process_class() " + cls_type_name);
		}
	}

}
