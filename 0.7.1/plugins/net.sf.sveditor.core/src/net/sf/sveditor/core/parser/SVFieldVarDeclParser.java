/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVFieldVarDeclParser extends SVParserBase {
	
	public SVFieldVarDeclParser(ISVParser parser) {
		super(parser);
	}
	
	/**
	 * Checks to see if this is a declaration. Parses and returns if so. 
	 * 
	 * @param decl_allowed
	 * @return
	 */
	public boolean try_parse(ISVDBAddChildItem parent, boolean decl_allowed) throws SVParseException {
		if ((fLexer.peekKeyword(SVKeywords.fBuiltinTypes) && !fLexer.peekKeyword("void")) ||
				fLexer.isIdentifier() || fLexer.peekKeyword("typedef")) {
			boolean builtin_type = (fLexer.peekKeyword(SVKeywords.fBuiltinTypes) && !fLexer.peekKeyword("void"));
			
			if ((fLexer.peekKeyword(SVKeywords.fBuiltinTypes) && !fLexer.peekKeyword("void")) ||
					fLexer.peekKeyword("typedef")) {
				// Definitely a declaration
				if (!decl_allowed) {
					error("declaration in a post-declaration location");
				}
				parsers().blockItemDeclParser().parse(parent, null, null);
				return true;
			} else {
				// May be a declaration. Let's see
				
				// Variable declarations
				List<SVToken> id_list = parsers().SVParser().scopedStaticIdentifier_l(true);
			
				if (!builtin_type && (fLexer.peekOperator() && !fLexer.peekOperator("#"))) {
					// likely a statement
					for (int i=id_list.size()-1; i>=0; i--) {
						fLexer.ungetToken(id_list.get(i));
					}
					debug("non-declaration statement: " + fLexer.peek());
				} else {
					for (int i=id_list.size()-1; i>=0; i--) {
						fLexer.ungetToken(id_list.get(i));
					}
					debug("Pre-var parse: " + fLexer.peek());
					if (!decl_allowed) {
						error("declaration in a non-declaration location");
					}
					
					parsers().blockItemDeclParser().parse(parent, null, null);
				
					// Bail for now
					return true; 
				}
			}
		} else {
			
			// time to move on to the body
			debug("non-declaration statement: " + fLexer.peek());
		}
		
		return false;
	}

}
