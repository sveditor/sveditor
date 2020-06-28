/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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
		KW kw = fLexer.peekKeywordE();
		boolean builtin_type;
		if ((builtin_type = (SVKeywords.fBuiltinTypesE.contains(kw) && kw != KW.VOID)) ||
				fLexer.isIdentifier() || kw == KW.TYPEDEF) {
			
			if (builtin_type || kw == KW.TYPEDEF) {
				// Definitely a declaration
				if (!decl_allowed) {
					error("declaration in a post-declaration location");
				}
				parsers().blockItemDeclParser().parse(parent, null, -1);
				return true;
			} else {
				// May be a declaration. Let's see
				
				// Variable declarations
				List<SVToken> id_list = parsers().SVParser().scopedStaticIdentifier_l(true);
			
				if (!builtin_type && (fLexer.peekOperator() && !fLexer.peekOperator(OP.HASH))) {
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
					
					parsers().blockItemDeclParser().parse(parent, null, -1);
				
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
