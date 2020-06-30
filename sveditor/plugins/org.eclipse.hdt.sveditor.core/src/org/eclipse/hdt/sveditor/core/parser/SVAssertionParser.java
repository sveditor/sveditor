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


package org.eclipse.hdt.sveditor.core.parser;

import org.eclipse.hdt.sveditor.core.db.ISVDBAddChildItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBActionBlockStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBAssertStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBAssumeStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBCoverStmt;

public class SVAssertionParser extends SVParserBase {
	
	public SVAssertionParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBAssertStmt parse(ISVDBAddChildItem parent, String assertion_label) throws SVParseException {
		long start = fLexer.getStartLocation();
		
		KW assert_type = fLexer.readKeyword(KW.ASSERT, KW.ASSUME, KW.COVER, KW.EXPECT);
		SVDBAssertStmt assert_stmt;
		if (assert_type == KW.ASSERT || assert_type == KW.EXPECT) {
			assert_stmt = new SVDBAssertStmt();
			if (assertion_label != "")  {
				assert_stmt.setName(assertion_label);
			}
		} else if (assert_type == KW.ASSUME) {
			assert_stmt = new SVDBAssumeStmt();
		} else {
			assert_stmt = new SVDBCoverStmt();
			if (assertion_label != "")  {
				assert_stmt.setName(assertion_label);
			}
		}
		assert_stmt.setLocation(start);
		if (fDebugEn) {debug("assertion_stmt - " + fLexer.peek());}

		// Cover the following
		//   expect <some_property>
		//   assert property <some_property>
		if (fLexer.peekKeyword(KW.PROPERTY) || (assert_type.getImg().equals("expect"))) {
			
			if (fLexer.peekKeyword(KW.PROPERTY))
				fLexer.eatToken();
			fLexer.readOperator(OP.LPAREN);
			assert_stmt.setExpr(fParsers.propertyExprParser().property_spec());
			fLexer.readOperator(OP.RPAREN);
			/* TODO: Ignoring body of property for now
			fLexer.skipPastMatch("(", ")");
			 */
		} else {
			if (fLexer.peekOperator(OP.HASH)) {
				// TODO:
				fLexer.eatToken();
				fLexer.readNumber();
			}
			
			fLexer.readOperator(OP.LPAREN);
			assert_stmt.setExpr(parsers().exprParser().event_expression());
			fLexer.readOperator(OP.RPAREN);
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
