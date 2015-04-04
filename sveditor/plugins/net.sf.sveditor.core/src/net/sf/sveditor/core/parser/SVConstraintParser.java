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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBLiteralExpr;
import net.sf.sveditor.core.db.stmt.SVDBConstraintDistListItem;
import net.sf.sveditor.core.db.stmt.SVDBConstraintDistListStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintForeachStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintIfStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintImplStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintSetStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintSolveBeforeStmt;
import net.sf.sveditor.core.db.stmt.SVDBExprStmt;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.parser.SVLexer.Context;

public class SVConstraintParser extends SVParserBase {
	private List<SVToken>					fTmpTokenList;
	
	public SVConstraintParser(ISVParser parser) {
		super(parser);
		fTmpTokenList = new ArrayList<SVToken>();
	}
	
	public void parse(ISVDBAddChildItem parent, int qualifiers) throws SVParseException {
		SVDBConstraint c = new SVDBConstraint();
		c.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword("constraint");
		Context ctxt = fLexer.getContext();
		fLexer.setContext(Context.Constraint);
	
		try {
			c.setName(fParsers.SVParser().scopedIdentifier(false));

			// Forward declaration
			if (fLexer.peekOperator(";")) {
				fLexer.eatToken();
			} else {
				fLexer.readOperator("{");

				parent.addChildItem(c);

				while (fLexer.peek() != null && !fLexer.peekOperator("}")) {
					c.addChildItem(constraint_set_item());
				}

				c.setEndLocation(fLexer.getStartLocation());
				fLexer.readOperator("}");
			}
		} finally {
			fLexer.setContext(ctxt);
		}
	}

	/**
	 * 
	 * @param force_braces
	 * @param check_for_concat -- check whether for "if () {concat}" case
	 * @return
	 * @throws SVParseException
	 */
	public SVDBStmt constraint_set(boolean force_braces, boolean check_for_concat) throws SVParseException {
		if (fDebugEn) {debug("--> constraint_set()");}
		
		if (force_braces || fLexer.peekOperator("{")) {
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
						!fLexer.peekOperator(";", ",") &&
						!fLexer.peekKeyword("if", "else", "foreach", "inside")) {
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
				if (fLexer.peekOperator(",") ||
						(brace_balance == 0 && fLexer.peekOperator(";"))) {
				 */
				if ((brace_balance == 1 && fLexer.peekOperator(",") && paren_balance == 0) ||
						(brace_balance == 0 && fLexer.peekOperator(";"))) {
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
				SVDBStmt ret = constraint_set_item();
				if (fDebugEn) {debug("<-- constraint_set()");}
				return ret;
			} else {
				SVDBConstraintSetStmt ret = new SVDBConstraintSetStmt(); 
				fLexer.readOperator("{");
				while (lexer().peek() != null && !fLexer.peekOperator("}")) {
					SVDBStmt c_stmt = constraint_set_item();
					ret.addConstraintStmt(c_stmt);
				}
				fLexer.readOperator("}");
				if (fLexer.peekOperator(";"))  {
					fLexer.readOperator(";");		// Not documented in LRM that I can tell... Modelsim seens to need it though ... wrap this in an if (fLexer.peekOperator(";") {}?
				}
				if (fDebugEn) {debug("<-- constraint_set()");}
				return ret;
			}
		} else {
			if (fDebugEn) {debug("<-- constraint_set()");}
			return constraint_set_item();
		}
	}

	private SVDBStmt constraint_set_item() throws SVParseException {
		SVDBStmt ret = null;
		
		if (fDebugEn) { debug("--> constraint_set_item " + fLexer.peek()); }
		
		if (fLexer.peekKeyword("solve")) {
			ret = solve_expression();
		} else if (fLexer.peekKeyword("if")) {
			ret = constraint_if_expression();
		} else if (fLexer.peekKeyword("foreach")) {
			ret = constraint_foreach();
		} else {
			
			if (fLexer.peekKeyword("soft")) {
				fLexer.eatToken();
			}
			
			// Not sure. Possibly one of:
			// - expression_or_dist
			//     - expression [dist { dist_list }]
			// - expression -> constraint_set

			// tok = expression(tok);
			SVDBExpr expr = fParsers.exprParser().expression();
			
			if (fLexer.peekKeyword("dist")) {
				ret = dist_expr();
			} else if (fLexer.peekOperator(";")) {
				// Done
				fLexer.eatToken();
				ret = new SVDBExprStmt(expr);
			} else if (fLexer.peekOperator("->")) {
				if (fDebugEn) { debug("  implication"); }
				fLexer.eatToken();
				
				ret = new SVDBConstraintImplStmt(expr, constraint_set(false, true));
			} else if (fLexer.peekOperator("}")) {
				ret = new SVDBExprStmt(expr);
				// Do nothing ... expecting this
			} else {
				error("Unknown suffix for expression: " + fLexer.getImage());
			}
		}
		
		if (fDebugEn) { debug("<-- constraint_set_item " + fLexer.peek()); }
		
		return ret;
	}

	public SVDBConstraintDistListStmt dist_expr() throws SVParseException {
		SVDBConstraintDistListStmt dist_stmt = new SVDBConstraintDistListStmt();
		fLexer.readKeyword("dist");
		dist_list(dist_stmt);
		fLexer.readOperator(";");
		
		return dist_stmt;
	}
	
	public void dist_list(SVDBConstraintDistListStmt dist_stmt) throws SVParseException {
		fLexer.readOperator("{");
		SVDBConstraintDistListItem item = dist_item();
		dist_stmt.addDistItem(item);

		while (fLexer.peekOperator(",")) {
			fLexer.eatToken();
			
			item = dist_item();
		}
		fLexer.readOperator("}");
	}

	private SVDBConstraintDistListItem dist_item() throws SVParseException {
		SVDBConstraintDistListItem ret = new SVDBConstraintDistListItem();
	
		if (fLexer.peekOperator("[")) {
			ret.setLHS(fParsers.exprParser().parse_range());
		} else {
			ret.setLHS(fParsers.exprParser().expression());
		}

		if (fLexer.peekOperator(",", "}")) {
			ret.setIsDist(false);
			ret.setRHS(new SVDBLiteralExpr("1"));
		} else {
			String type = fLexer.readOperator(":=", ":/");
			ret.setIsDist(type.equals(":/"));
			ret.setRHS(fParsers.exprParser().expression());
		}

		return ret;
	}

	private SVDBConstraintIfStmt constraint_if_expression() throws SVParseException {
		SVDBConstraintIfStmt ret;
		if (fDebugEn) {debug("--> constraint_if_expression");}
		
		fLexer.eatToken(); // 'if'
		
		fLexer.readOperator("(");
		SVDBExpr if_expr = fParsers.exprParser().expression();
		fLexer.readOperator(")");
		
		SVDBStmt constraint = constraint_set(false, true);
		
		if (fLexer.peekKeyword("else")) {
			SVDBStmt else_stmt;
			fLexer.eatToken();
			if (fLexer.peekKeyword("if")) {
				else_stmt = constraint_if_expression();
			} else {
				else_stmt = constraint_set(false, true);
			}
			ret = new SVDBConstraintIfStmt(if_expr, constraint, else_stmt, true);
		} else {
			ret = new SVDBConstraintIfStmt(if_expr, constraint, null, false);
		}
		
		if (fDebugEn) {debug("<-- constraint_if_expression");}
		return ret;
	}

	private SVDBStmt constraint_foreach() throws SVParseException {
		SVDBConstraintForeachStmt stmt = new SVDBConstraintForeachStmt();
		stmt.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword("foreach");
		
		fLexer.readOperator("(");
		stmt.setExpr(fParsers.exprParser().foreach_loopvar());
		fLexer.readOperator(")");
		
		stmt.setStmt(constraint_set(false, true));
		
		return stmt;
	}
	
	private SVDBConstraintSolveBeforeStmt solve_expression() throws SVParseException {
		SVDBConstraintSolveBeforeStmt ret = new SVDBConstraintSolveBeforeStmt();
		fLexer.eatToken();
		
		// solve <var> {, <var>} ...
		SVDBExpr expr = fParsers.exprParser().variable_lvalue();
		ret.addSolveBefore(expr);
		
		while (fLexer.peekOperator(",")) {
			fLexer.eatToken(); // ,
			ret.addSolveBefore(fParsers.exprParser().variable_lvalue());
		}
		
		// solve <var> before ...
		fLexer.readKeyword("before");
		
		ret.addSolveAfter(fParsers.exprParser().variable_lvalue());
		
		while (fLexer.peekOperator(",")) {
			fLexer.eatToken(); // ,
			ret.addSolveAfter(fParsers.exprParser().variable_lvalue());
		}
		
		fLexer.readOperator(";");
		
		return ret;
	}
	

}
