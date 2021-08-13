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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.ISVDBAddChildItem;
import org.eclipse.hdt.sveditor.core.db.SVDBConstraint;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBExpr;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBLiteralExpr;
import org.eclipse.hdt.sveditor.core.db.expr.SVDBOpenRangeListExpr;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBConstraintDistListItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBConstraintDistListStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBConstraintForeachStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBConstraintIfStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBConstraintImplStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBConstraintSetStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBConstraintSolveBeforeStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBConstraintUniqueStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBExprStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBStmt;
import org.eclipse.hdt.sveditor.core.parser.SVLexer.Context;

public class SVConstraintParser extends SVParserBase {
	private List<SVToken>					fTmpTokenList;
	
	public SVConstraintParser(ISVParser parser) {
		super(parser);
		fTmpTokenList = new ArrayList<SVToken>();
	}
	
	public void parse(ISVDBAddChildItem parent, int qualifiers) throws SVParseException {
		SVDBConstraint c = new SVDBConstraint();
		c.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword(KW.CONSTRAINT);
		Context ctxt = fLexer.setContext(Context.Constraint);
	
		try {
			c.setName(fParsers.SVParser().scopedIdentifier(false));

			// Forward declaration
			if (fLexer.peekOperator(OP.SEMICOLON)) {
				fLexer.eatToken();
			} else {
				fLexer.readOperator(OP.LBRACE);

				parent.addChildItem(c);

				while (fLexer.peek() != null && !fLexer.peekOperator(OP.RBRACE)) {
					c.addChildItem(constraint_set_item());
				}

				c.setEndLocation(fLexer.getStartLocation());
				fLexer.readOperator(OP.RBRACE);
			}
		} finally {
			fLexer.setContext(ctxt);
		}
	}

	/**
	 * 
	 * @param force_braces
	 * @param check_for_concat -- check whether for "if () {concat}" case
	 * @param top_level -- true if this is a top-level constraint set, such as the body of a constraint declaration
	 * @return
	 * @throws SVParseException
	 */
	public SVDBStmt constraint_set(boolean force_braces, boolean check_for_concat, boolean top_level) throws SVParseException {
		if (fDebugEn) {debug("--> constraint_set()");}
		
		if (force_braces || fLexer.peekOperator(OP.LBRACE)) {
			boolean is_concat = false;
			
			// Checks to see if what initially appears to be a constraint set block
			// is actually a concat expression
			if (check_for_concat) {
				String tok;
				int brace_balance = 0;
				int paren_balance = 0;
				fTmpTokenList.clear();
				// Scan forward to the first ';' ',' or brace
				while ((tok = fLexer.peek()) != null && 
						!fLexer.peekOperator(OP.SEMICOLON, OP.COMMA) &&
						!fLexer.peekKeyword(KW.IF, KW.ELSE, KW.FOREACH, KW.INSIDE)) {
					if (tok.equals("{")) {
						brace_balance++;
					} else if (tok.equals("}")) {
						brace_balance--;
					} else if (tok.equals("(")) {
						paren_balance++;
					} else if (tok.equals(")")) {
						paren_balance--;
					}
					
					fTmpTokenList.add(fLexer.consumeToken());
					
					if (brace_balance == 0) {
						break;
					}
				}

				/*
				if (fLexer.peekOperator(OP.COMMA) ||
						(brace_balance == 0 && fLexer.peekOperator(OP.SEMICOLON))) {
				 */
				if ((brace_balance == 1 && fLexer.peekOperator(OP.COMMA) && paren_balance == 0) ||
						(brace_balance == 0 && fLexer.peekOperator(OP.SEMICOLON))) {
					// Yes, very likely a concat
					if (fDebugEn) {
						debug("Likely concatenation: tok=" + fLexer.peek() + " brace_balance=" + brace_balance);
					}
					is_concat = true;
				} else {
					if (fDebugEn) {
						debug("Not concatenation: tok=" + fLexer.peek() + " brace_balance=" + brace_balance);
					}
				}
				fLexer.ungetToken(fTmpTokenList);
			}

			if (is_concat) {
				if (fDebugEn) {debug(" -- is_concat");}
				SVDBStmt ret = constraint_set_item();
				if (fDebugEn) {debug("<-- constraint_set()");}
				return ret;
			} else {
				SVDBConstraintSetStmt ret = new SVDBConstraintSetStmt(); 
				fLexer.readOperator(OP.LBRACE);
				while (lexer().peek() != null && !fLexer.peekOperator(OP.RBRACE)) {
					SVDBStmt c_stmt = constraint_set_item();
					ret.addConstraintStmt(c_stmt);
				}
				fLexer.readOperator(OP.RBRACE);
				if (!top_level && fLexer.peekOperator(OP.SEMICOLON))  {
					// Not documented in LRM that I can tell... Modelsim seems to allow it though... wrap this in an if (fLexer.peekOperator(OP.SEMICOLON) {}?				
					fLexer.readOperator(OP.SEMICOLON);		
				}
				if (fDebugEn) {debug("<-- constraint_set()");}
				return ret;
			}
		} else {
			SVDBStmt ret = constraint_set_item();
			if (fDebugEn) {debug("<-- constraint_set()");}
			return ret;
		}
	}

	private SVDBStmt constraint_set_item() throws SVParseException {
		SVDBStmt ret = null;
		
		if (fDebugEn) { debug("--> constraint_set_item " + fLexer.peek()); }

	
		KW kw = fLexer.peekKeywordE();
		if (fDebugEn) { debug(" -- kw=" + kw); }
		if (kw != null) {
			switch (kw) {
				case SOLVE:
					ret = solve_expression();
					break;
				case IF: 
					ret = constraint_if_expression();
					break;
				case FOREACH:
					ret = constraint_foreach();
					break;
				
				case UNIQUE:
					ret = constraint_unique();
					break;
					
				default: {
					ret = expr_constraint();
					} break;
			}
		} else {
			ret = expr_constraint();
		}
		
		if (fDebugEn) { debug("<-- constraint_set_item " + fLexer.peek()); }
		
		return ret;
	}
	
	private SVDBStmt expr_constraint() throws SVParseException {
		SVDBStmt ret = null;
		
		Context ctxt = fLexer.setContext(Context.Constraint);
		
		if (fDebugEn) { debug("--> expr_constraint " + fLexer.peek()); }
		
		try {

			if (fLexer.peekKeyword(KW.SOFT)) {
				fLexer.eatToken();
			}
			SVDBExpr expr = fParsers.exprParser().expression();

			if (fLexer.peekKeyword(KW.DIST)) {
				ret = dist_expr();
			} else if (fLexer.peekOperator(OP.SEMICOLON)) {
				// Done
				fLexer.eatToken();
				ret = new SVDBExprStmt(expr);
			} else if (fLexer.peekOperator(OP.IMPL)) {
				if (fDebugEn) { debug("  implication"); }
				fLexer.eatToken();

				ret = new SVDBConstraintImplStmt(expr, constraint_set(false, true, false));
			} else if (fLexer.peekOperator(OP.RBRACE)) {
				ret = new SVDBExprStmt(expr);
				// Do nothing ... expecting this
			} else {
				error("Unknown suffix for expression: " + fLexer.getImage());
			}
		} finally {
			fLexer.setContext(ctxt);
		}
		
		if (fDebugEn) { debug("<-- expr_constraint " + fLexer.peek()); }
		return ret;
	}

	public SVDBConstraintDistListStmt dist_expr() throws SVParseException {
		SVDBConstraintDistListStmt dist_stmt = new SVDBConstraintDistListStmt();
		fLexer.readKeyword(KW.DIST);
		dist_list(dist_stmt);
		fLexer.readOperator(OP.SEMICOLON);
		
		return dist_stmt;
	}
	
	public void dist_list(SVDBConstraintDistListStmt dist_stmt) throws SVParseException {
		fLexer.readOperator(OP.LBRACE);
		SVDBConstraintDistListItem item = dist_item();
		dist_stmt.addDistItem(item);

		while (fLexer.peekOperator(OP.COMMA)) {
			fLexer.eatToken();
			
			item = dist_item();
		}
		fLexer.readOperator(OP.RBRACE);
	}

	private SVDBConstraintDistListItem dist_item() throws SVParseException {
		SVDBConstraintDistListItem ret = new SVDBConstraintDistListItem();
	
		if (fLexer.peekOperator(OP.LBRACKET)) {
			ret.setLHS(fParsers.exprParser().parse_range());
		} else {
			ret.setLHS(fParsers.exprParser().expression());
		}

		if (fLexer.peekOperator(OP.COMMA, OP.RBRACE)) {
			ret.setIsDist(false);
			ret.setRHS(new SVDBLiteralExpr("1"));
		} else {
			OP type = fLexer.readOperator(OP.COLON_EQ, OP.COLON_DIV);
			ret.setIsDist(type.equals(OP.COLON_DIV));
			ret.setRHS(fParsers.exprParser().expression());
		}

		return ret;
	}

	private SVDBConstraintIfStmt constraint_if_expression() throws SVParseException {
		SVDBConstraintIfStmt ret;
		if (fDebugEn) {debug("--> constraint_if_expression");}
		
		fLexer.eatToken(); // 'if'
		
		fLexer.readOperator(OP.LPAREN);
		SVDBExpr if_expr = fParsers.exprParser().expression();
		fLexer.readOperator(OP.RPAREN);
		
		SVDBStmt constraint = constraint_set(false, true, false);
		
		if (fLexer.peekKeyword(KW.ELSE)) {
			SVDBStmt else_stmt;
			fLexer.eatToken();
			if (fLexer.peekKeyword(KW.IF)) {
				else_stmt = constraint_if_expression();
			} else {
				else_stmt = constraint_set(false, true, false);
			}
			ret = new SVDBConstraintIfStmt(if_expr, constraint, else_stmt, true);
		} else {
			ret = new SVDBConstraintIfStmt(if_expr, constraint, null, false);
		}
		
		if (fDebugEn) {debug("<-- constraint_if_expression");}
		return ret;
	}

	/**
	 * uniqueness_constraint ::= unique { open_range_list } ;
	 * @return
	 * @throws SVParseException
	 */
	private SVDBStmt constraint_unique() throws SVParseException {
		if (fDebugEn) { debug("--> constraint_unique"); }
		SVDBConstraintUniqueStmt stmt = new SVDBConstraintUniqueStmt();
		stmt.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword(KW.UNIQUE);
		
		fLexer.readOperator(OP.LBRACE);
		
		SVDBOpenRangeListExpr range_list = new SVDBOpenRangeListExpr();
		fParsers.exprParser().open_range_list_1(range_list.getRangeList());
		stmt.setExpr(range_list);

		fLexer.readOperator(OP.RBRACE);
		fLexer.readOperator(OP.SEMICOLON);
		
		if (fDebugEn) { debug("<-- constraint_unique"); }

		return stmt;
	}
	
	private SVDBStmt constraint_foreach() throws SVParseException {
		if (fDebugEn) { debug("--> constraint_foreach"); }
		SVDBConstraintForeachStmt stmt = new SVDBConstraintForeachStmt();
		stmt.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword(KW.FOREACH);
		
		fLexer.readOperator(OP.LPAREN);
		stmt.setExpr(fParsers.exprParser().foreach_loopvar());
		fLexer.readOperator(OP.RPAREN);
		
		stmt.setStmt(constraint_set(false, true, false));
		
		if (fDebugEn) { debug("<-- constraint_foreach"); }
		return stmt;
	}
	
	private SVDBConstraintSolveBeforeStmt solve_expression() throws SVParseException {
		SVDBConstraintSolveBeforeStmt ret = new SVDBConstraintSolveBeforeStmt();
		fLexer.eatToken();
		
		// solve <var> {, <var>} ...
		SVDBExpr expr = fParsers.exprParser().variable_lvalue();
		ret.addSolveBefore(expr);
		
		while (fLexer.peekOperator(OP.COMMA)) {
			fLexer.eatToken(); // ,
			ret.addSolveBefore(fParsers.exprParser().variable_lvalue());
		}
		
		// solve <var> before ...
		fLexer.readKeyword(KW.BEFORE);
		
		ret.addSolveAfter(fParsers.exprParser().variable_lvalue());
		
		while (fLexer.peekOperator(OP.COMMA)) {
			fLexer.eatToken(); // ,
			ret.addSolveAfter(fParsers.exprParser().variable_lvalue());
		}
		
		fLexer.readOperator(OP.SEMICOLON);
		
		return ret;
	}
	

}
