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

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.stmt.SVDBActionBlockStmt;
import net.sf.sveditor.core.db.stmt.SVDBAssertStmt;
import net.sf.sveditor.core.db.stmt.SVDBAssumeStmt;
import net.sf.sveditor.core.db.stmt.SVDBCoverStmt;

public class SVAssertionParser extends SVParserBase {
	
	public SVAssertionParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBAssertStmt parse(ISVDBAddChildItem parent) throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		
		String assert_type = fLexer.readKeyword("assert", "assume", "cover", "expect");
		SVDBAssertStmt assert_stmt;
		if (assert_type.equals("assert") || (assert_type.equals ("expect"))) {
			assert_stmt = new SVDBAssertStmt();
		} else if (assert_type.equals("assume")) {
			assert_stmt = new SVDBAssumeStmt();
		} else {
			assert_stmt = new SVDBCoverStmt();
		}
		assert_stmt.setLocation(start);
		if (fDebugEn) {debug("assertion_stmt - " + fLexer.peek());}

		// Cover the following
		//   expect <some_property>
		//   assert property <some_property>
		if (fLexer.peekKeyword("property") || (assert_type.equals("expect"))) {
			
			if (fLexer.peekKeyword("property"))
				fLexer.eatToken();
			fLexer.readOperator("(");
			assert_stmt.setExpr(fParsers.propertyExprParser().property_spec());
			fLexer.readOperator(")");
			/* TODO: Ignoring body of property for now
			fLexer.skipPastMatch("(", ")");
			 */
		} else {
			if (fLexer.peekOperator("#")) {
				// TODO:
				fLexer.eatToken();
				fLexer.readNumber();
			}
			
			fLexer.readOperator("(");
			assert_stmt.setExpr(parsers().exprParser().event_expression());
			fLexer.readOperator(")");
		}
		
		parent.addChildItem(assert_stmt);
		
		assert_stmt.setActionBlock(new SVDBActionBlockStmt());
		if (assert_type.equals("cover")) {
			// Only supports stmt_or_null
			parsers().behavioralBlockParser().action_block_stmt(assert_stmt.getActionBlock());
		} else {
			parsers().behavioralBlockParser().action_block(assert_stmt.getActionBlock());
		}
		
		return assert_stmt;
	}
	

}
