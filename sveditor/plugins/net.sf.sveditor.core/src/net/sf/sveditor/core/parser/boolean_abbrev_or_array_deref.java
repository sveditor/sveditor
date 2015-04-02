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

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.expr.SVDBArrayAccessExpr;
import net.sf.sveditor.core.db.expr.SVDBBinaryExpr;
import net.sf.sveditor.core.db.expr.SVDBCycleDelayExpr;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBFirstMatchExpr;
import net.sf.sveditor.core.db.expr.SVDBIdentifierExpr;
import net.sf.sveditor.core.db.expr.SVDBLiteralExpr;
import net.sf.sveditor.core.db.expr.SVDBPropertyCaseItem;
import net.sf.sveditor.core.db.expr.SVDBPropertyCaseStmt;
import net.sf.sveditor.core.db.expr.SVDBPropertyIfStmt;
import net.sf.sveditor.core.db.expr.SVDBPropertySpecExpr;
import net.sf.sveditor.core.db.expr.SVDBPropertyWeakStrongExpr;
import net.sf.sveditor.core.db.expr.SVDBRangeExpr;
import net.sf.sveditor.core.db.expr.SVDBSequenceClockingExpr;
import net.sf.sveditor.core.db.expr.SVDBSequenceCycleDelayExpr;
import net.sf.sveditor.core.db.expr.SVDBSequenceDistExpr;
import net.sf.sveditor.core.db.expr.SVDBSequenceMatchItemExpr;
import net.sf.sveditor.core.db.expr.SVDBSequenceRepetitionExpr;
import net.sf.sveditor.core.db.expr.SVDBUnaryExpr;

public class boolean_abbrev_or_array_deref extends SVParserBase {
	
	public boolean_abbrev_or_array_deref(ISVParser parser) {
		super(parser);
	}
	
	private static final Set<String> BinaryOpKW;
	private static final Set<String> BinaryOp;
	
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
		
		BinaryOp = new HashSet<String>();
		BinaryOp.add("|->");
		BinaryOp.add("|=>");
		BinaryOp.add("#-#");
		BinaryOp.add("#-#");
		for (String op : SVOperators.RelationalOps) {
			BinaryOp.add(op);
		}
	}
	
	public SVDBExpr property_statement() throws SVParseException {
		if (fDebugEn) { debug("--> property_statement() " + fLexer.peek()); }
		SVDBExpr ret;
		if (fLexer.peekKeyword("if")) {
			ret = property_statement_if();
		} else if (fLexer.peekKeyword("case")) {
			ret = property_stmt_case();
		} else {
			SVDBExpr stmt = property_expr();
			fLexer.readOperator(";");
			ret = stmt;
		}
		
		if (fDebugEn) { debug("<-- property_statement() " + fLexer.peek()); }
		return ret;
	}
	
	public SVDBExpr property_expr() throws SVParseException {
		SVDBExpr ret = null;
		if (fDebugEn) {debug("--> property_expr() " + fLexer.peek());}
		if (fLexer.peekKeyword("strong","weak")) {
			// weak_strong_expr
			SVDBPropertyWeakStrongExpr ws_expr = new SVDBPropertyWeakStrongExpr();
			ws_expr.setLocation(fLexer.getStartLocation());
			
			String ws = fLexer.eatToken();
			ws_expr.setIsWeak(ws.equals("weak"));
			fLexer.readOperator("(");
			ws_expr.setExpr(fParsers.propertyExprParser().sequence_expr());
			fLexer.readOperator(")");
			ret = ws_expr;
		} else if (fLexer.peekOperator("(")) {
			fLexer.eatToken();
			
			SVDBExpr p_expr = property_expr();
			fLexer.readOperator(")");
			
			if (p_expr == null) {
				error("Property expression is null");
			}

			if (fDebugEn) {
				debug("inner expr: " + p_expr.getClass().getName());
			}

			// Some ambiguity between sequence-match expression
			// and a paren property expression
			if (fLexer.peekOperator(",")) {
				SVDBSequenceMatchItemExpr match_expr = new SVDBSequenceMatchItemExpr();
				match_expr.setExpr(p_expr);
				while (fLexer.peekOperator(",")) {
					fLexer.eatToken();
					match_expr.addMatchItemExpr(sequence_match_item());
				}
				/*
				fLexer.readOperator(")");
				
				if (fLexer.peekOperator("[")) {
					match_expr.setSequenceAbbrev(sequence_abbrev());
				}
				 */
				ret = match_expr;
			} else {
				SVDBSequenceMatchItemExpr match_expr = new SVDBSequenceMatchItemExpr();
				match_expr.setExpr(p_expr);
				
				if (fLexer.peekOperator("[")) {
//					match_expr.setSequenceAbbrev(sequence_abbrev());
					match_expr.setSequenceAbbrev(boolean_abbrev());
				}
				
				ret = match_expr;
				if (fDebugEn) {debug("  post SVDBParenExpr: " + fLexer.peek());}
			}
		} else if (fLexer.peekKeyword("not")) {
			// not expression
			SVDBUnaryExpr unary_expr = new SVDBUnaryExpr();
			unary_expr.setLocation(fLexer.getStartLocation());
			
			fLexer.eatToken();
			unary_expr.setOp("not");
			unary_expr.setExpr(fParsers.propertyExprParser().property_expr());
			ret = unary_expr;
		} else if (fLexer.peekKeyword("nexttime", "s_nexttime")) {
			// nexttime expression
		} else if (fLexer.peekKeyword("always", "s_always", "eventually", "s_eventually")) {
			// always/eventually expression
		} else if (fLexer.peekKeyword("accept_on", "reject_on", "sync_accept_on", "sync_reject_on")) {
			// 
		} else if (fLexer.peekKeyword("if","case")) {
			ret = property_statement();
		} else {
			// TODO: property_statement, property_instance, clocking_event
			if (fDebugEn) { debug("  property_expr --> sequence_expr() " + fLexer.peek()); }
			ret = sequence_expr();
			if (fDebugEn) { debug("  property_expr <-- sequence_expr() " + fLexer.peek()); }
		}
		
		// Now, parse binary operators
		if (fLexer.peekKeyword(BinaryOpKW) || fLexer.peekOperator(BinaryOp)) {
			String op = fLexer.eatToken();
			if (fDebugEn) {debug("Property binary operator: " + op);}
			ret = new SVDBBinaryExpr(ret, op, property_expr());
		} else if (fLexer.peekOperator("##")) {
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
			
			if (fLexer.peekKeyword(BinaryOpKW) || fLexer.peekOperator(BinaryOp)) {
				op = fLexer.eatToken();
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
		fLexer.readKeyword("if");
		
		fLexer.readOperator("(");
		stmt.setExpr(expression_or_dist());
		fLexer.readOperator(")");
		
		stmt.setIfExpr(property_expr());
		
		if (fLexer.peekKeyword("else")) {
			fLexer.eatToken();
			stmt.setElseExpr(property_expr());
		}
	
		return stmt;
	}
	
	private SVDBExpr property_stmt_case() throws SVParseException {
		SVDBPropertyCaseStmt stmt = new SVDBPropertyCaseStmt();
		stmt.setLocation(fLexer.getStartLocation());
		
		fLexer.readKeyword("case");
		
		fLexer.readOperator("(");
		stmt.setExpr(expression_or_dist());
		fLexer.readOperator(")");
		
		while (fLexer.peek() != null && !fLexer.peekKeyword("endcase")) {
			SVDBPropertyCaseItem case_item = property_stmt_case_item();
			stmt.addItem(case_item);
		}
		fLexer.readKeyword("endcase");
		
		return stmt;
	}
	
	private SVDBPropertyCaseItem property_stmt_case_item() throws SVParseException {
		if (fDebugEn) {
			debug("--> property_stmt_case_item " + fLexer.peek());
		}
		SVDBPropertyCaseItem item = new SVDBPropertyCaseItem();
		item.setLocation(fLexer.getStartLocation());
	
		if (fLexer.peekKeyword("default")) {
			fLexer.eatToken();
			item.addExpr(new SVDBIdentifierExpr("default"));
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
			}
		} else {
			while (fLexer.peek() != null) {
				item.addExpr(expression_or_dist());
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
			
			fLexer.readOperator(":");
		}
	
		item.setStmt(property_statement());
		
		if (fDebugEn) {
			debug("<-- property_stmt_case_item " + fLexer.peek());
		}
		return item;
	}
	
	public SVDBExpr sequence_expr() throws SVParseException {
		SVDBExpr expr = null;
		if (fDebugEn) {debug("--> sequence_expr() " + fLexer.peek());}
		if (fLexer.peekOperator("##")) {
			if (fDebugEn) { debug("  cycle_delay"); }
			// cycle_delay_range sequence_expr { cycle_delay_range sequence_expr }
			while (fLexer.peekOperator("##")) {
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
		} else if (fLexer.peekOperator("@")) {
			// clocking_event sequence_expr
			SVDBSequenceClockingExpr clk_expr = new SVDBSequenceClockingExpr();
			clk_expr.setLocation(fLexer.getStartLocation());
			clk_expr.setClockingExpr(fParsers.exprParser().clocking_event());
			clk_expr.setSequenceExpr(sequence_expr());
			expr = clk_expr;
		} else if (fLexer.peekOperator("(")) {
			// ( sequence_expr {, sequence_match_item} ) [sequence_abbrev]
			// (expression) [dist]
			if (fDebugEn) {
				debug("entering sequence_expr {...}");
			}
			SVDBSequenceMatchItemExpr match_expr = new SVDBSequenceMatchItemExpr();

			if (fDebugEn) { debug("  --> sequence_expr enter paren"); }
			fLexer.readOperator("(");
			match_expr.setExpr(sequence_expr());
			while (fLexer.peekOperator(",")) {
				fLexer.eatToken();
				match_expr.addMatchItemExpr(sequence_match_item());
			}
			fLexer.readOperator(")");
			if (fDebugEn) { debug("  <-- sequence_expr enter paren"); }
			
			if (fLexer.peekOperator("[")) {
//				match_expr.setSequenceAbbrev(sequence_abbrev());
				match_expr.setSequenceAbbrev(boolean_abbrev());
			}
			expr = match_expr;
		} else if (fLexer.peekKeyword("first_match")) {
			// first_match ( sequence_expr {, sequence_match_item} )
			SVDBFirstMatchExpr first_match = new SVDBFirstMatchExpr();
			first_match.setLocation(fLexer.getStartLocation());
			fLexer.eatToken();
			
			fLexer.readOperator("(");
			first_match.setExpr(sequence_expr());
			while (fLexer.peekOperator(",")) {
				fLexer.eatToken();
				first_match.addSequenceMatchItem(sequence_match_item());
			}
			fLexer.readOperator(")");
			expr = first_match;
		} else if (fLexer.peekOperator(")")) {
			// fall through
			if (fDebugEn) { debug(" -- Operator == ) ; fall through"); }
		} else {
			//   expression_or_dist [boolean_abbrev]
			// | expression_or_dist throughout sequence_expr 
			expr = expression_or_dist();
			
			if (fLexer.peekOperator("[")) {
				// TODO: where to hang this?
				SVDBExpr bool_abbrev = boolean_abbrev();
			} else if (fLexer.peekOperator("@")) {
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
		if (fLexer.peekOperator("##")) {
			while (fLexer.peekOperator("##")) {
				SVDBSequenceCycleDelayExpr delay_expr = new SVDBSequenceCycleDelayExpr();
				delay_expr.setLocation(fLexer.getStartLocation());
				fLexer.eatToken();
				delay_expr.setLhs(expr);
				delay_expr.setDelay(cycle_delay_range());
				delay_expr.setRhs(sequence_expr());
				expr = delay_expr;
			}
		} else if (fLexer.peekKeyword("and","intersect","or","within","throughout") ||
				fLexer.peekOperator(SVOperators.RelationalOps)) {
			SVDBLocation start = fLexer.getStartLocation();
			if (fDebugEn) {debug(" --> -- binary sequence_expr" + fLexer.peek());}
			expr = new SVDBBinaryExpr(expr, fLexer.eatToken(), sequence_expr());
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

		fLexer.readOperator("[");
		if (fLexer.peekOperator("*")) {
			fLexer.eatToken();
			expr.setRepType("*");
			// ] | const_or_range_expr
			if (!fLexer.peekOperator("]")) {
				expr.setExpr(fParsers.exprParser().const_or_range_expression());
			}
		} else if (fLexer.peekOperator("+")) {
			fLexer.eatToken();
			expr.setRepType("+");
		} else if (fLexer.peekOperator("=")) {
			fLexer.eatToken();
			expr.setRepType("=");
			expr.setExpr(fParsers.exprParser().const_or_range_expression());
		} else if (fLexer.peekOperator("->")) {
			fLexer.eatToken();
			expr.setRepType("->");
			expr.setExpr(fParsers.exprParser().const_or_range_expression());
		} else {
			// Just an array dereference
			ret = fParsers.exprParser().expression();
			
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				ret = new SVDBArrayAccessExpr(null, ret, 
						fParsers.exprParser().expression());
			} else {
				ret = new SVDBArrayAccessExpr(null, ret, null);
			}
		}
		fLexer.readOperator("]");
		return ret;
	}

	private SVDBExpr expression_or_dist() throws SVParseException {
		if (fDebugEn) { debug("--> expression_or_dist " + fLexer.peek()); }
		SVDBExpr expr = fParsers.exprParser().assert_expression();
		if (fDebugEn) { debug("  post assert_expression " + fLexer.peek()); }
		if (fLexer.peekKeyword("dist")) {
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
		fLexer.readOperator("[");
		if (fLexer.peekOperator("*")) {
			fLexer.eatToken();
			if (fLexer.peekOperator("]")) {
				expr = new SVDBLiteralExpr("*");
			} else {
				expr = fParsers.exprParser().expression();
				if (fLexer.peekOperator(":")) {
					fLexer.eatToken();
					expr = new SVDBRangeExpr(expr, fParsers.exprParser().expression());
				}
			}
		} else {
			fLexer.readOperator("+");
			expr = new SVDBLiteralExpr("+");
		}
		fLexer.readOperator("]");
		return expr;
	}
	
	private SVDBCycleDelayExpr cycle_delay_range() throws SVParseException {
		SVDBCycleDelayExpr expr = new SVDBCycleDelayExpr();
		expr.setLocation(fLexer.getStartLocation());
		
		// [cycle_delay_const_range_expression]
		if (fLexer.peekOperator("[")) {
			fLexer.eatToken();
			if (fLexer.peekOperator("*","+")) {
				String op = fLexer.eatToken();
				expr.setExpr(new SVDBRangeExpr(
						new SVDBLiteralExpr(op), new SVDBLiteralExpr(op)));
			} else {
				SVDBExpr expr1 = fParsers.exprParser().expression();
				fLexer.readOperator(":");
				if (fLexer.peekOperator("$")) {
					fLexer.eatToken();
					expr.setExpr(new SVDBRangeExpr(expr1, new SVDBLiteralExpr("$")));
				} else {
					expr.setExpr(new SVDBRangeExpr(expr1, fParsers.exprParser().expression()));
				}
			}
			fLexer.readOperator("]");
		}
		// (constant_expression)
		else if (fLexer.peekOperator("(")) {
			fLexer.readOperator("(");
			expr.setExpr(fParsers.exprParser().assert_expression());
			fLexer.readOperator(")");
		} else {
			expr.setExpr(fParsers.exprParser().assert_expression());
		}
		
		return expr;
	}
	
	public SVDBPropertySpecExpr property_spec() throws SVParseException {
		SVDBPropertySpecExpr expr = new SVDBPropertySpecExpr();
		expr.setLocation(fLexer.getStartLocation());
		if (fLexer.peekOperator("@")) {
			expr.setClockingEvent(fParsers.exprParser().clocking_event());
		}
		
		if (fLexer.peekKeyword("disable")) {
			fLexer.readKeyword("disable");
			fLexer.readKeyword("iff");
			fLexer.readOperator("(");

			// TODO: should be expression or dist
			expr.setDisableExpr(fParsers.exprParser().assert_expression());
			fLexer.readOperator(")");
		}
		expr.setExpr(fParsers.propertyExprParser().property_expr());
		
		return expr;
	}
}
