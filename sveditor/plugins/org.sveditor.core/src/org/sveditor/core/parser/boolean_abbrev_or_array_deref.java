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


package org.sveditor.core.parser;

import java.util.HashSet;
import java.util.Set;

import org.sveditor.core.db.SVDBItemType;
import org.sveditor.core.db.expr.SVDBArrayAccessExpr;
import org.sveditor.core.db.expr.SVDBBinaryExpr;
import org.sveditor.core.db.expr.SVDBClockedPropertyExpr;
import org.sveditor.core.db.expr.SVDBCycleDelayExpr;
import org.sveditor.core.db.expr.SVDBExpr;
import org.sveditor.core.db.expr.SVDBFirstMatchExpr;
import org.sveditor.core.db.expr.SVDBIdentifierExpr;
import org.sveditor.core.db.expr.SVDBLiteralExpr;
import org.sveditor.core.db.expr.SVDBPropertyCaseItem;
import org.sveditor.core.db.expr.SVDBPropertyCaseStmt;
import org.sveditor.core.db.expr.SVDBPropertyIfStmt;
import org.sveditor.core.db.expr.SVDBPropertySpecExpr;
import org.sveditor.core.db.expr.SVDBPropertyWeakStrongExpr;
import org.sveditor.core.db.expr.SVDBRangeExpr;
import org.sveditor.core.db.expr.SVDBSequenceClockingExpr;
import org.sveditor.core.db.expr.SVDBSequenceCycleDelayExpr;
import org.sveditor.core.db.expr.SVDBSequenceDistExpr;
import org.sveditor.core.db.expr.SVDBSequenceMatchItemExpr;
import org.sveditor.core.db.expr.SVDBSequenceRepetitionExpr;
import org.sveditor.core.db.expr.SVDBUnaryExpr;
import org.sveditor.core.parser.ISVKeywords.KW;
import org.sveditor.core.parser.ISVOperators.OP;

public class boolean_abbrev_or_array_deref extends SVParserBase {
	
	public boolean_abbrev_or_array_deref(ISVParser parser) {
		super(parser);
	}
	
	private static final Set<String> BinaryOpKW;
	private static final Set<KW> BinaryOpKWE;
	private static final Set<OP> BinaryOp;
	
	static {
		BinaryOpKW = new HashSet<String>();
		BinaryOpKW.add("or");
		BinaryOpKW.add("and");
		BinaryOpKW.add("throughout");
		BinaryOpKW.add("until");
		BinaryOpKW.add("within");
		BinaryOpKW.add("s_until");
		BinaryOpKW.add("until_with");
		BinaryOpKW.add("s_until_with");
		BinaryOpKW.add("implies");
		BinaryOpKW.add("iff");

		BinaryOpKWE = new HashSet<KW>();
		BinaryOpKWE.add(KW.OR);
		BinaryOpKWE.add(KW.AND);
		BinaryOpKWE.add(KW.THROUGHOUT);
		BinaryOpKWE.add(KW.UNTIL);
		BinaryOpKWE.add(KW.WITHIN);
		BinaryOpKWE.add(KW.S_UNTIL);
		BinaryOpKWE.add(KW.UNTIL_WITH);
		BinaryOpKWE.add(KW.S_UNTIL_WITH);
		BinaryOpKWE.add(KW.IMPLIES);
		BinaryOpKWE.add(KW.IFF);
		
		BinaryOp = new HashSet<OP>();
		BinaryOp.add(OP.OR_IMPL);
		BinaryOp.add(OP.OR_EQ_GT);
		BinaryOp.add(OP.HASH_SUB_HASH);
		for (OP op : SVOperators.RelationalOps) {
			BinaryOp.add(op);
		}
	}
	
	public SVDBExpr property_statement() throws SVParseException {
		if (fDebugEn) { debug("--> property_statement() " + fLexer.peek()); }
		SVDBExpr ret;
		KW kw = fLexer.peekKeywordE();
		
		if (kw != null) {
			switch (kw) {
				case IF: ret = property_statement_if(); break;
				case CASE: ret = property_stmt_case(); break;
				default: {
					SVDBExpr stmt = property_expr();
					fLexer.readOperator(OP.SEMICOLON);
					ret = stmt;
				} break;
			}
		} else {
			SVDBExpr stmt = property_expr();
			fLexer.readOperator(OP.SEMICOLON);
			ret = stmt;
		}
		
		if (fDebugEn) { debug("<-- property_statement() " + fLexer.peek()); }
		return ret;
	}
	
	public SVDBExpr property_expr() throws SVParseException {
		SVDBExpr ret = null;
		if (fDebugEn) {debug("--> property_expr() " + fLexer.peek());}
		
		KW kw = fLexer.peekKeywordE();
		
		if (kw != null) {
			switch (kw) {
				case STRONG:
				case WEAK: {
					// weak_strong_expr
					SVDBPropertyWeakStrongExpr ws_expr = new SVDBPropertyWeakStrongExpr();
					ws_expr.setLocation(fLexer.getStartLocation());
					
					fLexer.eatToken();
					ws_expr.setIsWeak(kw == KW.WEAK);
					fLexer.readOperator(OP.LPAREN);
					ws_expr.setExpr(fParsers.propertyExprParser().sequence_expr());
					fLexer.readOperator(OP.RPAREN);
					ret = ws_expr;	
				} break;
				
				case NOT: {
					// not expression
					SVDBUnaryExpr unary_expr = new SVDBUnaryExpr();
					unary_expr.setLocation(fLexer.getStartLocation());
					
					fLexer.eatToken();
					unary_expr.setOp("not");
					unary_expr.setExpr(fParsers.propertyExprParser().property_expr());
					ret = unary_expr;					
				} break;
				
				case IF:
				case CASE: {
					ret = property_statement();
				} break;
				case FIRST_MATCH: {
					// first_match ( sequence_expr {, sequence_match_item} )
					SVDBFirstMatchExpr first_match = new SVDBFirstMatchExpr();
					first_match.setLocation(fLexer.getStartLocation());
					fLexer.eatToken();
					
					fLexer.readOperator(OP.LPAREN);
					first_match.setExpr(sequence_expr());
					while (fLexer.peekOperator(OP.COMMA)) {
						fLexer.eatToken();
						first_match.addSequenceMatchItem(sequence_match_item());
					}
					fLexer.readOperator(OP.RPAREN);
					ret = first_match;
				} break;

//		} else if (fLexer.peekKeyword("nexttime", "s_nexttime")) {
//			// nexttime expression
//		} else if (fLexer.peekKeyword("always", "s_always", "eventually", "s_eventually")) {
//			// always/eventually expression
//		} else if (fLexer.peekKeyword("accept_on", "reject_on", "sync_accept_on", "sync_reject_on")) {
				default:
					error("Unhandled property_expr keyword");
					break;
			}
		} else { // kw null

			if (fLexer.peekOperator(OP.LPAREN)) {
				fLexer.eatToken();

				SVDBExpr p_expr = property_expr();
				fLexer.readOperator(OP.RPAREN);

				if (p_expr == null) {
					error("Property expression is null");
				}

				if (fDebugEn) {
					debug("inner expr: " + p_expr.getClass().getName());
				}

				// Some ambiguity between sequence-match expression
				// and a paren property expression
				if (fLexer.peekOperator(OP.COMMA)) {
					SVDBSequenceMatchItemExpr match_expr = new SVDBSequenceMatchItemExpr();
					match_expr.setExpr(p_expr);
					while (fLexer.peekOperator(OP.COMMA)) {
						fLexer.eatToken();
						match_expr.addMatchItemExpr(sequence_match_item());
					}
					/*
				fLexer.readOperator(OP.RPAREN);

				if (fLexer.peekOperator(OP.LBRACKET)) {
					match_expr.setSequenceAbbrev(sequence_abbrev());
				}
					 */
					ret = match_expr;
				} else {
					SVDBSequenceMatchItemExpr match_expr = new SVDBSequenceMatchItemExpr();
					match_expr.setExpr(p_expr);

					if (fLexer.peekOperator(OP.LBRACKET)) {
						//					match_expr.setSequenceAbbrev(sequence_abbrev());
						match_expr.setSequenceAbbrev(boolean_abbrev());
					}

					ret = match_expr;
					if (fDebugEn) {debug("  post SVDBParenExpr: " + fLexer.peek());}
				}

			} else if (fLexer.peekOperator(OP.AT)) {
				SVDBClockedPropertyExpr expr = new SVDBClockedPropertyExpr();
				expr.setClockingExpr(fParsers.exprParser().clocking_event());
				expr.setPropertyExpr(property_expr());
				ret = expr;
			} else {
				// TODO: property_statement, property_instance, clocking_event
				if (fDebugEn) { debug("  property_expr --> sequence_expr() " + fLexer.peek()); }
				ret = sequence_expr();
				// A sequence expression can be followed by a , results in sequence_match expression
				if (fLexer.peekOperator(OP.COMMA)) {
					SVDBSequenceMatchItemExpr match_expr = new SVDBSequenceMatchItemExpr();
					match_expr.setExpr(ret);
					while (fLexer.peekOperator(OP.COMMA)) {
						fLexer.eatToken();
						match_expr.addMatchItemExpr(sequence_match_item());
					}
					ret = match_expr;
				}
				if (fDebugEn) { debug("  property_expr <-- sequence_expr() " + fLexer.peek()); }
			}
		}
		
		// Now, parse binary operators
		if (fLexer.peekKeyword(BinaryOpKWE) || fLexer.peekOperator(BinaryOp)) {
			String op = fLexer.eatTokenR();
			if (fDebugEn) {debug("Property binary operator: " + op);}
			ret = new SVDBBinaryExpr(ret, op, property_expr());
		} else if (fLexer.peekOperator(OP.HASH2)) {
//			SVDBExpr expr = sequence_expr();
			SVToken op_t = fLexer.consumeToken();
			String op;
			
			// Could be ## or ##1
			if (fLexer.peek() != null && fLexer.peek().equals("1")) {
				fLexer.eatToken();
				op = "##1";
				ret = new SVDBBinaryExpr(ret, op, sequence_expr());
			} else {
				op = op_t.getImage();
				fLexer.ungetToken(op_t);
				ret = new SVDBBinaryExpr(ret, op, sequence_expr());
			}
			
			if (fLexer.peekKeyword(BinaryOpKWE) || fLexer.peekOperator(BinaryOp)) {
				op = fLexer.eatTokenR();
				if (fDebugEn) {debug("Property binary operator: " + op);}
				ret = new SVDBBinaryExpr(ret, op, property_expr());
			}
		}
		
		if (fDebugEn) {debug("<-- property_expr() " + fLexer.peek());}
		
		return ret;
	}
	
	private SVDBExpr property_statement_if() throws SVParseException {
		SVDBPropertyIfStmt stmt = new SVDBPropertyIfStmt();
		stmt.setLocation(fLexer.getStartLocation());
		stmt.setType(SVDBItemType.PropertyIfStmt);
		fLexer.readKeyword(KW.IF);
		
		fLexer.readOperator(OP.LPAREN);
		stmt.setExpr(expression_or_dist());
		fLexer.readOperator(OP.RPAREN);
		
		stmt.setIfExpr(property_expr());
		
		if (fLexer.peekKeyword(KW.ELSE)) {
			fLexer.eatToken();
			stmt.setElseExpr(property_expr());
		}
	
		return stmt;
	}
	
	private SVDBExpr property_stmt_case() throws SVParseException {
		SVDBPropertyCaseStmt stmt = new SVDBPropertyCaseStmt();
		stmt.setLocation(fLexer.getStartLocation());
		
		fLexer.readKeyword(KW.CASE);
		
		fLexer.readOperator(OP.LPAREN);
		stmt.setExpr(expression_or_dist());
		fLexer.readOperator(OP.RPAREN);
		
		while (fLexer.peek() != null && !fLexer.peekKeyword(KW.ENDCASE)) {
			SVDBPropertyCaseItem case_item = property_stmt_case_item();
			stmt.addItem(case_item);
		}
		fLexer.readKeyword(KW.ENDCASE);
		
		return stmt;
	}
	
	private SVDBPropertyCaseItem property_stmt_case_item() throws SVParseException {
		if (fDebugEn) {
			debug("--> property_stmt_case_item " + fLexer.peek());
		}
		SVDBPropertyCaseItem item = new SVDBPropertyCaseItem();
		item.setLocation(fLexer.getStartLocation());
	
		if (fLexer.peekKeyword(KW.DEFAULT)) {
			fLexer.eatToken();
			item.addExpr(new SVDBIdentifierExpr("default"));
			if (fLexer.peekOperator(OP.COLON)) {
				fLexer.eatToken();
			}
		} else {
			while (fLexer.peek() != null) {
				item.addExpr(expression_or_dist());
				
				if (fLexer.peekOperator(OP.COMMA)) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
			
			fLexer.readOperator(OP.COLON);
		}
	
		item.setStmt(property_statement());
		
		if (fDebugEn) {
			debug("<-- property_stmt_case_item " + fLexer.peek());
		}
		return item;
	}
	
	/**
	 * sequence_expr ::=
	 *    cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
	 *    | sequence_expr cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
	 *    | expression_or_dist [ boolean_abbrev ]
	 *    | ( expression_or_dist {, sequence_match_item } ) [ boolean_abbrev ]
	 *    | sequence_instance [ sequence_abbrev ]
	 *    | ( sequence_expr {, sequence_match_item } ) [ sequence_abbrev ]
	 *    | sequence_expr and sequence_expr
	 *    | sequence_expr intersect sequence_expr
	 *    | sequence_expr or sequence_expr
	 *    | first_match ( sequence_expr {, sequence_match_item} )
	 *    | expression_or_dist throughout sequence_expr
	 *    | sequence_expr within sequence_expr
	 *    | clocking_event sequence_expr
	 *    
	 *    
	 * @return
	 * @throws SVParseException
	 */
	public SVDBExpr sequence_expr() throws SVParseException {
		SVDBExpr expr = null;
		if (fDebugEn) {debug("--> sequence_expr() " + fLexer.peek());}
		OP op;
		
		// LBRACE '{' could be a bus {a,b}, not an operator in this context
		// See bug #455
		if (((op = fLexer.peekOperatorE()) != null) && (op != OP.LBRACE)) {
			switch (op) {
				case HASH2: {
					if (fDebugEn) { debug("  cycle_delay"); }
					// cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
					while (fLexer.peekOperator(OP.HASH2)) {
						// TODO:
						SVDBSequenceCycleDelayExpr delay_expr = new SVDBSequenceCycleDelayExpr();
						delay_expr.setLocation(fLexer.getStartLocation());
						fLexer.eatToken();
						delay_expr.setLhs(expr);
						delay_expr.setDelay(cycle_delay_range());
						if (fDebugEn) { debug("  -- enter sequence_expr: " + fLexer.peek()); }
						delay_expr.setRhs(sequence_expr());
						expr = delay_expr;
					}
				} break;
				
				case AT: {
					// clocking_event sequence_expr
					SVDBSequenceClockingExpr clk_expr = new SVDBSequenceClockingExpr();
					clk_expr.setLocation(fLexer.getStartLocation());
					clk_expr.setClockingExpr(fParsers.exprParser().clocking_event());
					clk_expr.setSequenceExpr(sequence_expr());
					expr = clk_expr;
				} break;
				
				case LPAREN: {
					// ( sequence_expr {, sequence_match_item} ) [sequence_abbrev]
					// (expression) [dist]
					if (fDebugEn) {
						debug("entering sequence_expr {...}");
					}
					SVDBSequenceMatchItemExpr match_expr = new SVDBSequenceMatchItemExpr();

					if (fDebugEn) { debug("  --> sequence_expr enter paren"); }
					fLexer.readOperator(OP.LPAREN);
					match_expr.setExpr(sequence_expr());
					while (fLexer.peekOperator(OP.COMMA)) {
						fLexer.eatToken();
						match_expr.addMatchItemExpr(sequence_match_item());
					}
					fLexer.readOperator(OP.RPAREN);
					if (fDebugEn) { debug("  <-- sequence_expr enter paren"); }

					if (fLexer.peekOperator(OP.LBRACKET)) {
						//				match_expr.setSequenceAbbrev(sequence_abbrev());
						match_expr.setSequenceAbbrev(boolean_abbrev());
					}
					expr = match_expr;
				} break;
				
				case RPAREN: {
					if (fDebugEn) { debug(" -- Operator == ) ; fall through"); }
				} break;
				
				case LBRACE: {
					if (fDebugEn) { debug(" -- Operator == ) ; fall through"); }
				} break;
				
				default:
					// Fall Through
//					error("unexpected operator: " + op);
					break;
			}
		} else if (fLexer.peekKeyword(KW.FIRST_MATCH)) {
			// first_match ( sequence_expr {, sequence_match_item} )
			SVDBFirstMatchExpr first_match = new SVDBFirstMatchExpr();
			first_match.setLocation(fLexer.getStartLocation());
			fLexer.eatToken();
			
			fLexer.readOperator(OP.LPAREN);
			first_match.setExpr(sequence_expr());
			while (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
				first_match.addSequenceMatchItem(sequence_match_item());
			}
			fLexer.readOperator(OP.RPAREN);
			expr = first_match;
		}
		
		// If we don't have one of the above ... try expression_or_dist
//		if (expr == null)  {
		else  {
			//   expression_or_dist [boolean_abbrev]
			// | expression_or_dist throughout sequence_expr 
			expr = expression_or_dist();
			
			if (fLexer.peekOperator(OP.LBRACKET)) {
				// TODO: where to hang this?
				SVDBExpr bool_abbrev = boolean_abbrev();
			} else if (fLexer.peekOperator(OP.AT)) {
				// Issue: #384 -- Appears a clocking event can follow an expression
				// TODO: Connect
				SVDBSequenceClockingExpr clk_expr = new SVDBSequenceClockingExpr();
				clk_expr.setLocation(fLexer.getStartLocation());
				clk_expr.setClockingExpr(fParsers.exprParser().clocking_event());
//				clk_expr.setSequenceExpr(sequence_expr());
			}/* else if (fLexer.peekKeyword("throughout")) {
				fLexer.eatToken();
				// TODO:
				sequence_expr();
			} */
		}
		
		// Trailing. sequence_expr 
		// ... cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
		// ... and sequence_expr
		// ... intersect sequence_expr
		// ... or sequence_expr
		// ... within sequence_expr
		if (fLexer.peekOperator(OP.HASH2)) {
			while (fLexer.peekOperator(OP.HASH2)) {
				SVDBSequenceCycleDelayExpr delay_expr = new SVDBSequenceCycleDelayExpr();
				delay_expr.setLocation(fLexer.getStartLocation());
				fLexer.eatToken();
				delay_expr.setLhs(expr);
				delay_expr.setDelay(cycle_delay_range());
				delay_expr.setRhs(sequence_expr());
				expr = delay_expr;
			}
		} else if (fLexer.peekKeyword(KW.AND, KW.INTERSECT, KW.OR, KW.WITHIN, KW.THROUGHOUT) ||
				fLexer.peekOperator(SVOperators.RelationalOpsE)) {
			long start = fLexer.getStartLocation();
			if (fDebugEn) {debug(" --> -- binary sequence_expr" + fLexer.peek());}
			expr = new SVDBBinaryExpr(expr, fLexer.eatTokenR(), sequence_expr());
			if (fDebugEn) {debug(" <-- -- binary sequence_expr" + fLexer.peek());}
			expr.setLocation(start);
		}
		
		if (fDebugEn) {debug("<-- sequence_expr() -- " + fLexer.peek());}
		
		return expr;
	}
	
	private SVDBExpr sequence_match_item() throws SVParseException {
		// inc_or_dec_expression
		//    <inc_or_dec_operator> variable_lval
		//    variable_lval inc_or_dec_operator
		// operator_assignment
		//    variable_lval assignment_operator expression
		// function_subroutine_call
		/*
		if (fLexer.peekOperator("--","++")) {
			
		} else {
			// variable_lvalue
			SVDBExpr lval = fParsers.exprParser().variable_lvalue();
			if (fLexer.peekOperator("--","++")) {
				// inc_dec_expr
			}
		}
		 */
		// TODO: for now, just return an expression
		return fParsers.exprParser().expression();
	}
	
	private SVDBExpr boolean_abbrev() throws SVParseException {
		SVDBSequenceRepetitionExpr expr = new SVDBSequenceRepetitionExpr();
		expr.setLocation(fLexer.getStartLocation());
		SVDBExpr ret = expr;

		fLexer.readOperator(OP.LBRACKET);
		if (fLexer.peekOperator(OP.MUL)) {
			fLexer.eatToken();
			expr.setRepType("*");
			// ] | const_or_range_expr
			if (!fLexer.peekOperator(OP.RBRACKET)) {
				expr.setExpr(fParsers.exprParser().const_or_range_expression());
			}
		} else if (fLexer.peekOperator(OP.PLUS)) {
			fLexer.eatToken();
			expr.setRepType("+");
		} else if (fLexer.peekOperator(OP.EQ)) {
			fLexer.eatToken();
			expr.setRepType("=");
			expr.setExpr(fParsers.exprParser().const_or_range_expression());
		} else if (fLexer.peekOperator(OP.IMPL)) {
			fLexer.eatToken();
			expr.setRepType("->");
			expr.setExpr(fParsers.exprParser().const_or_range_expression());
		} else {
			// Just an array dereference
			ret = fParsers.exprParser().expression();
			
			if (fLexer.peekOperator(OP.COLON, OP.PLUS_COLON, OP.SUB_COLON)) {
				fLexer.eatToken();
				ret = new SVDBArrayAccessExpr(null, ret, 
						fParsers.exprParser().expression());
			} else {
				ret = new SVDBArrayAccessExpr(null, ret, null);
			}
		}
		fLexer.readOperator(OP.RBRACKET);
		return ret;
	}

	private SVDBExpr expression_or_dist() throws SVParseException {
		if (fDebugEn) { debug("--> expression_or_dist " + fLexer.peek()); }
		SVDBExpr expr = fParsers.exprParser().assert_expression();
		if (fDebugEn) { debug("  post assert_expression " + fLexer.peek()); }
		if (fLexer.peekKeyword(KW.DIST)) {
			SVDBSequenceDistExpr dist = new SVDBSequenceDistExpr();
			dist.setLocation(fLexer.getStartLocation());
			dist.setDistExpr(fParsers.constraintParser().dist_expr());
			dist.setExpr(expr);
			expr = dist;
		}
		
		if (fDebugEn) { debug("<-- expression_or_dist " + fLexer.peek()); }
		return expr;
	}
	
	private SVDBExpr sequence_abbrev() throws SVParseException {
		// TODO: may need a special-purpose expression for this	
		SVDBExpr expr;
		fLexer.readOperator(OP.LBRACKET);
		if (fLexer.peekOperator(OP.MUL)) {
			fLexer.eatToken();
			if (fLexer.peekOperator(OP.RBRACKET)) {
				expr = new SVDBLiteralExpr("*");
			} else {
				expr = fParsers.exprParser().expression();
				if (fLexer.peekOperator(OP.COLON)) {
					fLexer.eatToken();
					expr = new SVDBRangeExpr(expr, fParsers.exprParser().expression());
				}
			}
		} else {
			fLexer.readOperator(OP.PLUS);
			expr = new SVDBLiteralExpr("+");
		}
		fLexer.readOperator(OP.RBRACKET);
		return expr;
	}
	
	private SVDBCycleDelayExpr cycle_delay_range() throws SVParseException {
		SVDBCycleDelayExpr expr = new SVDBCycleDelayExpr();
		expr.setLocation(fLexer.getStartLocation());
		
		// [cycle_delay_const_range_expression]
		if (fLexer.peekOperator(OP.LBRACKET)) {
			fLexer.eatToken();
			if (fLexer.peekOperator(OP.MUL, OP.PLUS)) {
				String op = fLexer.eatTokenR();
				expr.setExpr(new SVDBRangeExpr(
						new SVDBLiteralExpr(op), new SVDBLiteralExpr(op)));
			} else {
				SVDBExpr expr1 = fParsers.exprParser().expression();
				fLexer.readOperator(OP.COLON);
				if (fLexer.peekOperator(OP.DOLLAR)) {
					fLexer.eatToken();
					expr.setExpr(new SVDBRangeExpr(expr1, new SVDBLiteralExpr("$")));
				} else {
					expr.setExpr(new SVDBRangeExpr(expr1, fParsers.exprParser().expression()));
				}
			}
			fLexer.readOperator(OP.RBRACKET);
		}
		// (constant_expression)
		else if (fLexer.peekOperator(OP.LPAREN)) {
			fLexer.eatToken();
			expr.setExpr(fParsers.exprParser().assert_expression());
			fLexer.readOperator(OP.RPAREN);
		} else {
			expr.setExpr(fParsers.exprParser().assert_expression());
		}
		
		return expr;
	}
	
	public SVDBPropertySpecExpr property_spec() throws SVParseException {
		SVDBPropertySpecExpr expr = new SVDBPropertySpecExpr();
		expr.setLocation(fLexer.getStartLocation());
		if (fLexer.peekOperator(OP.AT)) {
			expr.setClockingEvent(fParsers.exprParser().clocking_event());
		}
		
		if (fLexer.peekKeyword(KW.DISABLE)) {
			fLexer.eatToken();
			fLexer.readKeyword(KW.IFF);
			fLexer.readOperator(OP.LPAREN);

			// TODO: should be expression or dist
			expr.setDisableExpr(fParsers.exprParser().assert_expression());
			fLexer.readOperator(OP.RPAREN);
		}
		expr.setExpr(fParsers.propertyExprParser().property_expr());
		
		return expr;
	}
}
