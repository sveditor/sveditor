/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.parser;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.expr.SVArrayAccessExpr;
import net.sf.sveditor.core.db.expr.SVAssignExpr;
import net.sf.sveditor.core.db.expr.SVAssignmentPatternExpr;
import net.sf.sveditor.core.db.expr.SVAssignmentPatternRepeatExpr;
import net.sf.sveditor.core.db.expr.SVBinaryExpr;
import net.sf.sveditor.core.db.expr.SVCastExpr;
import net.sf.sveditor.core.db.expr.SVConcatenationExpr;
import net.sf.sveditor.core.db.expr.SVCondExpr;
import net.sf.sveditor.core.db.expr.SVConstraintIfExpr;
import net.sf.sveditor.core.db.expr.SVConstraintSetExpr;
import net.sf.sveditor.core.db.expr.SVCoverBinsExpr;
import net.sf.sveditor.core.db.expr.SVCoverageExpr;
import net.sf.sveditor.core.db.expr.SVCoverpointExpr;
import net.sf.sveditor.core.db.expr.SVDistItemExpr;
import net.sf.sveditor.core.db.expr.SVDistListExpr;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.expr.SVExprParseException;
import net.sf.sveditor.core.db.expr.SVExprString;
import net.sf.sveditor.core.db.expr.SVExprUtils;
import net.sf.sveditor.core.db.expr.SVFieldAccessExpr;
import net.sf.sveditor.core.db.expr.SVIdentifierExpr;
import net.sf.sveditor.core.db.expr.SVImplicationExpr;
import net.sf.sveditor.core.db.expr.SVIncDecExpr;
import net.sf.sveditor.core.db.expr.SVInsideExpr;
import net.sf.sveditor.core.db.expr.SVLiteralExpr;
import net.sf.sveditor.core.db.expr.SVNullLiteralExpr;
import net.sf.sveditor.core.db.expr.SVParenExpr;
import net.sf.sveditor.core.db.expr.SVQualifiedSuperFieldRefExpr;
import net.sf.sveditor.core.db.expr.SVQualifiedThisRefExpr;
import net.sf.sveditor.core.db.expr.SVRandomizeCallExpr;
import net.sf.sveditor.core.db.expr.SVRangeExpr;
import net.sf.sveditor.core.db.expr.SVSolveBeforeExpr;
import net.sf.sveditor.core.db.expr.SVStringExpr;
import net.sf.sveditor.core.db.expr.SVSuperExpr;
import net.sf.sveditor.core.db.expr.SVTFCallExpr;
import net.sf.sveditor.core.db.expr.SVThisExpr;
import net.sf.sveditor.core.db.expr.SVUnaryExpr;
import net.sf.sveditor.core.scanner.SVKeywords;
import net.sf.sveditor.core.scanutils.ITextScanner;

public class SVExprParser extends SVParserBase {
//	private SVExprDump						fExprDump;
//	private boolean							fDebugEn = false;
	public static boolean					fUseFullExprParser = true;
	
	public SVExprParser(ISVParser parser) {
		super(parser);
//		fExprDump = new SVExprDump(System.out);
	}

	/**
	 * Expression := AssignmentExpression
	 * @param tok
	 * @return
	 * @throws SVParseException
	 */
	public SVExpr expression() throws SVParseException {
		SVExpr expr = null;
		if (fUseFullExprParser) {
			debug("--> expression()");
			expr = assignmentExpression();
			debug("<-- expression() " + expr);
		} else {
			expr = new SVExprString(parsers().SVParser().readExpression(true));
		}
		
		return expr; 
	}

	/**
	 * This method exists to support the old 'readExpression' method
	 * that scans expressions textually
	 * 
	 * @param accept_colon
	 * @return
	 * @throws SVParseException
	 */
	@Deprecated
	public SVExpr expression(boolean accept_colon) throws SVParseException {
		SVExpr expr = null;
		if (fUseFullExprParser) {
			debug("--> expression()");
			expr = assignmentExpression();
			debug("<-- expression() " + expr);
		} else {
			expr = new SVExprString(parsers().SVParser().readExpression(accept_colon));
		}
		
		return expr; 
	}

	/*
	@Deprecated
	public void init(final ITextScanner scanner) {
		lexer().init(new ISVParser() {
			
			public void warning(String msg, int lineno) {
			}
			
			public SVLexer lexer() {
				// TODO Auto-generated method stub
				return lexer();
			}
			
			public boolean error_limit_reached() {
				return true;
			}
			
			public void error(SVParseException e) {}
			
			public void error(String msg) {}

			public SVParsers parsers() {
				return null;
			}
			
			public void debug(String msg, Exception e) {}
			
		}, scanner); 
	}
	 */
	

	/**
	 * 
	 * parse_constraint()
	 * 
	 * Parse the body of a constraint statement
	 * 
	 * @param in
	 * @return
	 * @throws SVExprParseException
	 */
	@Deprecated
	public List<SVExpr> parse_constraint(ITextScanner in) throws SVExprParseException {
// TODO:		init(in);
		
		List<SVExpr> ret = new ArrayList<SVExpr>();

		try {
			SVExpr expr;
			
			while (peek() != null && !peek().equals("")) {
				debug("top of while: peek=" + peek());
				expr = constraint_block_item();
				
				if (expr != null) {
					try {
						ret.add(expr);
					} catch (Exception e) {
						System.out.println("expr is of type " + expr.getClass().getName());
						System.out.println("    expr: " + SVExprUtils.getDefault().exprToString(expr));
						throw e;
					}
				} else {
					System.out.println("[FIXME] null expr");
				}
			}
		} catch (EOFException e) {
			// ignore
		} catch (Exception e) {
			e.printStackTrace();
			System.out.println("[ERROR] " + e.getMessage());
			throw new SVExprParseException(e);
		}
		
		return ret;
	}
	
	/**
	 * parse_expression()
	 * 
	 * Parse a SV expression 
	 * 
	 * @param in
	 * @return
	 * @throws SVExprParseException
	 */
	@Deprecated
	public SVExpr parse_expression(ITextScanner in) throws SVExprParseException {
//		init(in);
		SVExpr expr = null;
		
		try {
			expr = expression();
		} catch (Exception e) {
			// Problem
			System.out.println("[ERROR] " + e.getMessage());
			throw new SVExprParseException(e);
		}
		
		return expr;
	}
	
	/**
	 * Parse the description of the coverpoint target
	 * 
	 * @param coverpoint
	 */
	public void coverpoint_target(SVCoverpointExpr coverpoint) throws SVParseException {
		
		try {
			SVExpr target = expression();

			coverpoint.setTarget(target);

			if (peekKeyword("iff")) {
				eatToken();
				readOperator("(");
				SVExpr iff_expr = expression();
				readOperator(")");

				coverpoint.setIFFExpr(iff_expr);
			}
		} catch (EOFException e) {
			e.printStackTrace();
			// Ignore
		}
	}
	
	public void coverpoint_body(SVCoverpointExpr coverpoint) throws SVParseException {
		
		try {
			while (peekKeyword("wildcard", "bins", "ignore_bins", "illegal_bins",
					"option", "type_option")) {

				if (peekKeyword("option", "type_option")) {
					String kw = eatToken();

					readOperator(".");

					String option = readIdentifier();

					if (!lexer().peekString() && !lexer().peekNumber()) {
						error("unknown option value type \"" + peek() + "\"");
					}

					if (kw.equals("option")) {
						coverpoint.addOption(option, eatToken());
					} else {
						coverpoint.addTypeOption(option, eatToken());
					}
				} else {
					if (peekKeyword("wildcard")) {
						eatToken();
					}

					String bins_kw = readKeyword("bins", "ignore_bins", "illegal_bins");
					String bins_id = readIdentifier();

					SVCoverBinsExpr bins = new SVCoverBinsExpr(bins_id, bins_kw);

					if (peekOperator("[")) {
						eatToken();

						bins.setIsArray(true);

						if (!peekOperator("]")) {
							// read the inner expression
							bins.setArrayExpr(expression());
						}
						readOperator("]");
					}

					readOperator("=");

					if (peekOperator("{")) {
						open_range_list(bins.getRangeList());
					} else if (peekKeyword("default")) {
						eatToken();
						bins.setIsDefault(true);
					} else {
						error("Unsupported coverage expression: " + peek());
						// 'default' or 'default sequence'
						// ???
					}

					coverpoint.getCoverBins().add(bins);

					if (peekOperator(";")) {
						eatToken();
					}
				}
			}
		} catch (EOFException e ) {
			// Ignore
		}
	}
	
	public List<SVCoverageExpr> parse_covercross(InputStream in) throws SVParseException {
		return null;
	}
	
	
	/**
	 * p
	 * @return
	 * @throws SVExprParseException
	 * @throws SVParseException
	 */
	
	public SVExpr constraint_block_item() throws SVParseException {
		SVExpr ret = null;
		
		if (peekKeyword("solve")) {
			// TODO: do actual parse
			ret = solve_expression();
		} else {
			ret = constraint_expression();
		}
		
		return ret;
	}
	
	
	public SVExpr constraint_expression() throws SVParseException {
		SVExpr ret = null;
		
		debug("--> constraint_expression()");
		
		if (peekKeyword("if")) {
			ret = constraint_if_expression();
		} else if (peekKeyword("foreach")) {
			// TODO:
			error("foreach unhandled");
		} else {
			// Not sure. Possibly one of:
			// - expression_or_dist
			//     - expression [dist { dist_list }]
			// - expression -> constraint_set

			// tok = expression(tok);
			SVExpr expr = expression();
			
			lexer().peek();
			
			/*
			if (fDebugEn) {
				System.out.print("expr=");
				fExprDump.dump(expr);
				System.out.println();
			}
			 */
			
			if (peekKeyword("dist")) {
				eatToken();
				readOperator("{");
				SVDistListExpr dist = dist_list();
				dist.setLHS(expr);
				readOperator("}");
				readOperator(";");
				
				ret = dist;
			} else if (peekOperator(";")) {
				// Done
				eatToken();
				ret = expr;
			} else if (peekOperator("->")) {
				eatToken();
				
				ret = new SVImplicationExpr(expr, constraint_set());
			} else {
				error("Unknown suffix for expression: " + lexer().getImage());
			}
		}
		
		debug("<-- constraint_expression()");
		
		return ret;
	}
	
	public SVDistListExpr dist_list() throws SVParseException {
		SVDistListExpr ret = new SVDistListExpr();
		SVDistItemExpr item = dist_item();
		ret.addDistItem(item);

		while (peekOperator(",")) {
			eatToken();
			
			item = dist_item();
		}
		
		return ret;
	}
	
	// constraint sc_mode_dist_c {sc_mode dist { 0 := 6, [1:2] := 2, [3:5] :/ 2};}
	
	public SVDistItemExpr dist_item() throws SVParseException {
		SVDistItemExpr ret = new SVDistItemExpr();
	
		if (peekOperator("[")) {
			ret.setLHS(parse_range());
		} else {
			ret.setLHS(expression());
		}

		if (peekOperator(",", "}")) {
			ret.setIsDist(false);
			ret.setRHS(new SVLiteralExpr("1"));
		} else {
			String type = readOperator(":=", ":/");
			ret.setIsDist(type.equals(":/"));
			ret.setRHS(expression());
		}

		return ret;
	}
	
	/**
	 * ConstraintIfExpression ::=
	 *     if ( expression ) ConstraintSet [else ConstraintSet]
	 * @return
	 * @throws SVParseException
	 */
	public SVConstraintIfExpr constraint_if_expression() throws SVParseException {
		SVConstraintIfExpr ret;
		debug("--> constraint_if_expression");
		
		eatToken(); // 'if'
		
		readOperator("(");
		SVExpr if_expr = expression();
		readOperator(")");
		
		SVConstraintSetExpr constraint = constraint_set();
		
		if (peekKeyword("else")) {
			SVExpr else_expr;
			eatToken();
			if (peekKeyword("if")) {
				else_expr = constraint_if_expression();
			} else {
				else_expr = constraint_set();
			}
			ret = new SVConstraintIfExpr(if_expr, constraint, else_expr, true);
		} else {
			ret = new SVConstraintIfExpr(if_expr, constraint, null, false);
		}
		
		debug("<-- constraint_if_expression");
		return ret;
	}
	
	public SVConstraintSetExpr constraint_set() throws SVParseException {
		SVConstraintSetExpr ret = new SVConstraintSetExpr(); 
		debug("--> constraint_set()");
		
		if (peekOperator("{")) {
			eatToken();
			do {
				SVExpr c_expr = constraint_expression();
				if (c_expr != null) {
					ret.getConstraintList().add(c_expr);
				}
			} while (!peekOperator("}"));
			readOperator("}");
		} else {
			SVExpr c_expr = constraint_expression();
			if (c_expr != null) {
				ret.getConstraintList().add(c_expr);
			}
		}
		
		debug("<-- constraint_set()");
		return ret;
	}
	
	public SVExpr solve_expression() throws SVParseException {
		SVSolveBeforeExpr ret = new SVSolveBeforeExpr();
		eatToken();
		
		// solve <var> {, <var>} ...
		String sb_var = readIdentifier();
		ret.getSolveBeforeList().add(sb_var);
		
		while (peekOperator(",")) {
			eatToken(); // ,
			ret.getSolveBeforeList().add(readIdentifier());
		}
		
		// solve <var> before ...
		readKeyword("before");
		
		ret.getSolveAfterList().add(readIdentifier());
		
		while (peekOperator(",")) {
			eatToken(); // ,
			ret.getSolveAfterList().add(readIdentifier());
		}
		
		readOperator(";");
		
		return ret;
	}
	
	
	/**
	 * AssignmentExpression :=
	 * 		ConditionalExpression [ AssignmentOperator AssignmentExpression]
	 * 
	 * @return
	 * @throws SVParseException
	 */
	public SVExpr assignmentExpression() throws SVParseException {
		debug("--> assignmentExpression()");
		SVExpr a = conditionalExpression();
		
		if (peekOperator("=", "+=", "-=", "*=", "/=", "&=", "|=", "^=", "%=", "<<=", ">>=")) {
			String op = readOperator();
			SVExpr rhs = assignmentExpression();
			a = new SVAssignExpr(a, op, rhs);
		} else if (peekKeyword("inside")) {
			eatToken();
			SVInsideExpr inside = new SVInsideExpr(a);
			
			open_range_list(inside.getValueRangeList());
			
			a = inside;
		}

		debug("<-- assignmentExpression() " + a);
		return a;
	}
	
	public void open_range_list(List<SVExpr> list) throws SVParseException {
		readOperator("{");
		do {
			if (peekOperator(",")) {
				eatToken();
			}
			if (peekOperator("[")) {
				list.add(parse_range());
			} else {
				list.add(expression());
			}
		} while (peekOperator(","));
		readOperator("}");
	}
	
	public SVRangeExpr parse_range() throws SVParseException {
		readOperator("[");
		SVExpr left = expression();
		readOperator(":");
		SVExpr right = expression();
		readOperator("]");
		
		return new SVRangeExpr(left, right);
	}
	
	/**
	 * conditionalExpression ::=
	 *     conditionalOrExpression [ '?' Expression ':' ConditionalExpression]
	 * @return
	 * @throws SVParseException
	 */
	public SVExpr conditionalExpression() throws SVParseException {
		debug("--> conditionalExpression()");
		SVExpr a = conditionalOrExpression();
		
		if (!peekOperator("?")) return a;
		eatToken();
		
		SVExpr lhs = a;
		SVExpr mhs = expression();
		readOperator(":");
		
		SVExpr rhs = conditionalExpression();
		a = new SVCondExpr(lhs, mhs, rhs);
		debug("<-- conditionalExpression() " + a);
		return a;
	}
	
	/**
	 * conditionalOrExpression ::=
	 * 		conditionalAndExpression { '||' conditionalAndExpression }
	 * @return
	 * @throws SVParseException
	 */
	public SVExpr conditionalOrExpression() throws SVParseException {
		debug("--> conditionalOrExpression()");
		SVExpr a = conditionalAndExpression();
		
		while (peekOperator("||")) {
			eatToken();
			a = new SVBinaryExpr(a, "||", conditionalAndExpression());
		}
		
		debug("<-- conditionalOrExpression() " + a);
		return a;
	}
	
	/**
	 * conditionalAndExpression ::=
	 * 	inclusiveOrExpression { '&&' inclusiveOrExpression }
	 * @return
	 * @throws SVParseException
	 */
	public SVExpr conditionalAndExpression() throws SVParseException {
		SVExpr a = inclusiveOrExpression();
		
		while (peekOperator("&&")) {
			eatToken();
			a = new SVBinaryExpr(a, "&&", inclusiveOrExpression());
		}
		return a;
	}
	
	public SVExpr inclusiveOrExpression() throws SVParseException {
		SVExpr a = exclusiveOrExpression();
		
		while (peekOperator("|")) {
			eatToken();
			a = new SVBinaryExpr(a, "|", exclusiveOrExpression());
		}
		
		return a;
	}
	
	public SVExpr exclusiveOrExpression() throws SVParseException {
		SVExpr a = andExpression();
		
		while (peekOperator("^")) {
			eatToken();
			a = new SVBinaryExpr(a, "^", andExpression());
		}
		
		return a;
	}
	
	public SVExpr andExpression() throws SVParseException {
		SVExpr a = equalityExpression();
		
		while (peekOperator("&")) {
			eatToken();
			a = new SVBinaryExpr(a, "&", equalityExpression());
		}
		
		return a;
	}
	
	public SVExpr equalityExpression() throws SVParseException {
		SVExpr a = relationalExpression();
		
		while (peekOperator("==", "!=", "===", "!==", "==?", "!=?")) {
			a = new SVBinaryExpr(a, readOperator(), relationalExpression());
		}
		
		return a;
	}
	
	public SVExpr relationalExpression() throws SVParseException {
		SVExpr a = shiftExpression();
		
		while (peekOperator("<", ">", "<=", ">=")) {
			a = new SVBinaryExpr(a, readOperator(), shiftExpression());
		}
		
		return a;
	}
	
	public SVExpr shiftExpression() throws SVParseException {
		SVExpr a = additiveExpression();
		
		while (peekOperator("<<", ">>", ">>>")) {
			a = new SVBinaryExpr(a, readOperator(), additiveExpression());
		}
		
		return a;
	}
	
	public SVExpr additiveExpression() throws SVParseException {
		SVExpr a = multiplicativeExpression();
		
		while (peekOperator("+", "-")) {
			a = new SVBinaryExpr(a, readOperator(), multiplicativeExpression());
		}
		return a;
	}
	
	public SVExpr multiplicativeExpression() throws SVParseException {
		SVExpr a = unaryExpression();
		
		while (peekOperator("*", "/", "%")) {
			a = new SVBinaryExpr(a, readOperator(), unaryExpression());
		}
		return a;
	}
	
	public SVExpr unaryExpression() throws SVParseException {
		if (peekOperator("++", "--")) {
			return new SVIncDecExpr(readOperator(), unaryExpression());
		}
		if (peekOperator("+", "-", "~", "!", "&", "~&", "|", "~|", "^", "~^", "^~")) {
			return new SVUnaryExpr(readOperator(), unaryExpression());
		} else if (peekOperator("'")) {
			SVAssignmentPatternExpr ret_top = null;
			lexer().eatToken();
			lexer().readOperator("{");
			SVExpr expr1 = expression();
			
			if (lexer().peekOperator("{")) {
				// repetition
				SVAssignmentPatternRepeatExpr ret = new SVAssignmentPatternRepeatExpr(expr1);
				
				lexer().eatToken(); // {
				while (true) {
					SVExpr expr = expression();
					
					ret.getPatternList().add(expr);
					
					if (lexer().peekOperator(",")) {
						lexer().eatToken();
					} else {
						break;
					}
				}
				lexer().readOperator("}");
				ret_top = ret;
			} else {
				SVAssignmentPatternExpr ret = new SVAssignmentPatternExpr();
				ret.getPatternList().add(expr1);
				
				while (lexer().peekOperator(",")) {
					lexer().eatToken();
					SVExpr expr = expression();

					ret.getPatternList().add(expr);
				}
				ret_top = ret;
			}
			lexer().readOperator("}");
			
			return ret_top;
		}
		
		SVExpr a = primary();
		
		if (lexer().peekOperator("'")) {
			lexer().eatToken();
			// MSB: new cast expression
			a = new SVCastExpr(a, expression());
		}
		
		while (peekOperator("::", ".", "[")) {
			a = selector(a);
		}
		
		while (peekOperator("++", "--")) {
			a = new SVIncDecExpr(readOperator(), a);
		}
		
		return a;
	}
	
	public SVExpr primary() throws SVParseException {
		debug("--> primary()");
		SVExpr ret = null;
		
		if (peekOperator("(")) {
			eatToken();
			
			// if (isType) {
			// TODO
			//
			
			SVExpr a = expression();
			readOperator(")");
			
			// cast
			// '(' expression() ')' unaryExpression
			peek();
			if (lexer().isNumber() || lexer().isIdentifier() ||
					peekOperator("(", "~", "!") ||
					peekKeyword("this", "super", "new")) {
				ret = new SVCastExpr(a, unaryExpression());
			} else {
				ret = new SVParenExpr(a);
			}
		} else {
			// TODO: must finish and figure out what's going on
			lexer().peek();
			if (lexer().isNumber()) {
				ret = new SVLiteralExpr(readNumber());
			} else if (lexer().peekString()) {
				ret = new SVStringExpr(lexer().eatToken());
			} else if (lexer().peekKeyword("null")) {
				lexer().eatToken();
				ret = new SVNullLiteralExpr();
			} else if (lexer().isIdentifier() || 
					SVKeywords.isBuiltInType(lexer().peek()) ||
					lexer().peekKeyword("new")) {
				debug("  primary \"" + lexer().getImage() + "\" is identifier or built-in type");
				String id = lexer().eatToken();
				
				if (peekOperator("(")) {
					if (id.equals("randomize")) {
						return randomize_call(null);
					} else {
						// Task/Function call
						return new SVTFCallExpr(null, id, arguments());
					}
				} else if (id.equals("new")) {
					return new SVTFCallExpr(null, id, new SVExpr[0]);
				} else {
					ret = new SVIdentifierExpr(id);
					debug("  after id-read: " + peek());
				}
			} else if (lexer().peekOperator("{")) {
				// concatenation
				ret = concatenation_or_repetition();
			} else if (peekKeyword("this")) {
				eatToken();
				return new SVThisExpr();
				/*
				if (peekOperator("(")) {
					// 'this' Arguments
					// Alternate constructor invocation
					// TODO: N/A??
				}
				error("Unhandled primary 'this'");
				 */
			} else if (peekKeyword("super")) {
				eatToken();
				return new SVSuperExpr();
				// error("Unhandled primary 'super'");
			} else if (peekKeyword("void")) {
				eatToken();
			} else {
				error("Unexpected token in primary: \"" + lexer().getImage() + "\"");
			}
		}
		
		debug("<-- primary() " + ret);
		return ret;
	}
	
	private SVExpr concatenation_or_repetition() throws SVParseException {
		readOperator("{");
		SVExpr expr = expression();
		
		if (lexer().peekOperator("{")) {
			lexer().eatToken();
			// repetition
			SVAssignmentPatternRepeatExpr ret = new SVAssignmentPatternRepeatExpr(expr);
			
			ret.getPatternList().add(expression());
			
			while (lexer().peekOperator(",")) {
				lexer().eatToken();
				ret.getPatternList().add(expression());
			}
			lexer().readOperator("}"); // end of inner expression
			lexer().readOperator("}");
			return ret;
		} else {
			SVConcatenationExpr ret = new SVConcatenationExpr();
			ret.getElements().add(expr);
			
			while (lexer().peekOperator(",")) {
				lexer().eatToken();
				ret.getElements().add(expression());
			}

			lexer().readOperator("}");

			return ret;
		}
	}
	
	public SVExpr [] arguments() throws SVParseException {
		readOperator("(");
		
		if (peekOperator(")")) {
			eatToken();
			return new SVExpr[0];
		}
		
		SVExpr arguments[] = argumentList();
		readOperator(")");
		
		return arguments;
	}
	
	public SVExpr [] argumentList() throws SVParseException {
		List<SVExpr> arguments = new ArrayList<SVExpr>();
		
		for (;;) {
			arguments.add(expression());
			if (!peekOperator(",")) {
				break;
			}
			eatToken();
		}
		return arguments.toArray(new SVExpr[arguments.size()]);
	}
	
	public SVExpr selector(SVExpr expr) throws SVParseException {
		if (peekOperator(".", "::")) {
			String q = eatToken();
			
			lexer().peek();
			if (lexer().isIdentifier()) {
				String id = lexer().readId();
				
				if (peekOperator("(")) {
					if (id.equals("randomize")) {
						return randomize_call(expr);
					} else {
						return new SVTFCallExpr(expr, id, arguments());
					}
				}
				// '.' identifier
				return new SVFieldAccessExpr(expr, (q.equals("::")), id);
			}
		}
		
		if (peekKeyword("this")) {
			// '.' 'this'
			eatToken();
			return new SVQualifiedThisRefExpr(expr);
		}
		if (peekKeyword("super")) {
			eatToken();
			/** Java-only -- qualified constructor invocation
			if (peekOperator("(")) {
				
			}
			 */
			readOperator(".");
			String id = readIdentifier();
			
			if (!peekOperator("(")) {
				// '.' super '.' identifier
				return new SVQualifiedSuperFieldRefExpr(expr, id);
			}
		}
		// TODO: keyword new
		// TODO: keyword class
		
		if (peekOperator("[")) {
			// '[' expression ']'
			eatToken();
			SVExpr low = expression();
			SVExpr high = null;
			
			// TODO: should probably preserve array-bounds method
			if (peekOperator(":", "+:", "-:")) {
				eatToken();
				high = expression();
			}
			
			readOperator("]");
			if (expr == null) {
				error("array expr == null");
			}
			return new SVArrayAccessExpr(expr, low, high);
		}
		
		error("Unexpected token \"" + lexer().getImage() + "\"");
		return null; // unreachable, since error always throws an exception
	}
	
	private SVRandomizeCallExpr randomize_call(SVExpr target) throws SVParseException {
		SVRandomizeCallExpr rand_call = new SVRandomizeCallExpr(target, "randomize", arguments());
		
		if (lexer().peekKeyword("with")) {
			lexer().eatToken();
			// constraint block
			rand_call.setWithBlock(constraint_set());
		}
		return rand_call;
	}
	
	private String peek() throws SVParseException {
		return lexer().peek();
	}

	private boolean peekOperator(String ... ops) throws SVParseException {
		return lexer().peekOperator(ops);
	}
	
	private String readOperator(String ... ops) throws SVParseException {
		return lexer().readOperator(ops);
	}
	
	private boolean peekKeyword(String ... kw) throws SVParseException {
		return lexer().peekKeyword(kw);
	}
	
	private String readKeyword(String ... kw) throws SVParseException {
		return lexer().readKeyword(kw);
	}
	
	private String readIdentifier() throws SVParseException {
		return lexer().readId();
	}
	
	private String readNumber() throws SVParseException {
		return lexer().readNumber();
	}
	
	private String eatToken() {
		return lexer().eatToken();
	}
}
