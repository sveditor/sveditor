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


package org.sveditor.core.parser;

import org.sveditor.core.db.IFieldItemAttr;
import org.sveditor.core.db.ISVDBAddChildItem;
import org.sveditor.core.db.SVDBClassDecl;
import org.sveditor.core.db.SVDBFieldItem;
import org.sveditor.core.db.SVDBLocation;
import org.sveditor.core.db.SVDBTypeInfoClassType;
import org.sveditor.core.parser.SVParseException.Kind;

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
			cls.addSuperClass(parsers().dataTypeParser().class_type());
			
			if ((qualifiers & SVDBFieldItem.FieldAttr_Interface) != 0) {
				// Interface class, so support multiple extension
				while (fLexer.peekOperator(OP.COMMA)) {
					fLexer.eatToken(); // eat the comma
					cls.addSuperClass(parsers().dataTypeParser().class_type());
				}
			}
		}
		
		if (fLexer.peekKeyword(KW.IMPLEMENTS)) {
			fLexer.eatToken();
			
			while (true) {
				cls.addImplements(parsers().dataTypeParser().class_type());
				
				if (fLexer.peekOperator(OP.COMMA)) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		}
		
		fLexer.readOperator(OP.SEMICOLON);
		
		parent.addChildItem(cls);

		try {
			enter_type_scope(cls);
			
			// TODO: need a better system here...
			while (fLexer.peek() != null && !fLexer.peekKeyword(KW.ENDCLASS)) {

				try {
					fParsers.modIfcBodyItemParser().parse(cls);
				} catch (SVParseException e) {
					SVToken last_tok; 
					
					if ((last_tok = fLexer.consumeToken()) == null) {
						throw new SVSkipToNextFileException();
					}
					SVToken tok;
					int fileid = SVDBLocation.unpackFileId(last_tok.getStartLocation());
					
					while ((tok = fLexer.consumeToken()) != null) {
						int fileid_1 = SVDBLocation.unpackFileId(tok.getStartLocation());
						
						if (tok.isOp(OP.SEMICOLON) || tok.isKW(KW.ENDCLASS)) {
							break;
						} else if (fileid != fileid_1) {
							// Delegate to the upper-level
							fLexer.ungetToken(tok);
							fLexer.ungetToken(last_tok);
							throw new SVSkipToNextFileException();
						}
						last_tok = tok;
					}
				}
			}
		} finally {
			leave_type_scope(cls);
		}

//		System.out.println("setClassEndLocation: " + 
//				SVDBLocation.toString(fLexer.getStartLocation()));
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
