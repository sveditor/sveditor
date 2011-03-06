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
import net.sf.sveditor.core.db.expr.SVClockingEventExpr;
import net.sf.sveditor.core.db.expr.SVConcatenationExpr;
import net.sf.sveditor.core.db.expr.SVCondExpr;
import net.sf.sveditor.core.db.expr.SVCoverBinsExpr;
import net.sf.sveditor.core.db.expr.SVCoverageExpr;
import net.sf.sveditor.core.db.expr.SVCoverpointExpr;
import net.sf.sveditor.core.db.expr.SVCtorExpr;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.expr.SVExprParseException;
import net.sf.sveditor.core.db.expr.SVExprString;
import net.sf.sveditor.core.db.expr.SVFieldAccessExpr;
import net.sf.sveditor.core.db.expr.SVIdentifierExpr;
import net.sf.sveditor.core.db.expr.SVIncDecExpr;
import net.sf.sveditor.core.db.expr.SVInsideExpr;
import net.sf.sveditor.core.db.expr.SVLiteralExpr;
import net.sf.sveditor.core.db.expr.SVNamedArgExpr;
import net.sf.sveditor.core.db.expr.SVNullLiteralExpr;
import net.sf.sveditor.core.db.expr.SVParenExpr;
import net.sf.sveditor.core.db.expr.SVQualifiedSuperFieldRefExpr;
import net.sf.sveditor.core.db.expr.SVQualifiedThisRefExpr;
import net.sf.sveditor.core.db.expr.SVRandomizeCallExpr;
import net.sf.sveditor.core.db.expr.SVRangeDollarBoundExpr;
import net.sf.sveditor.core.db.expr.SVRangeExpr;
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
	
	public SVClockingEventExpr clocking_event() throws SVParseException {
		SVClockingEventExpr expr = new SVClockingEventExpr();
		fLexer.readOperator("@");
		if (fLexer.peekOperator("(")) {
			expr.setExpr(event_expression());
		} else {
			expr.setExpr(new SVIdentifierExpr(fLexer.readId()));
		}
		
		return expr;
	}
	
	public SVExpr delay_expr() throws SVParseException {
		SVExpr expr = null;
		
		fLexer.readOperator("#");
		
		if (fLexer.peekOperator("(")) {
			fLexer.eatToken();
			expr = fParsers.exprParser().expression();
			fLexer.readOperator(")");
		} else {
			if (fLexer.peekNumber()) {
				expr = new SVLiteralExpr(fLexer.eatToken());
			} else if (fLexer.peekOperator("1step")) {
				expr = new SVLiteralExpr(fLexer.eatToken());
			} else if (fLexer.peekId()) {
				expr = new SVLiteralExpr(fLexer.eatToken());
			} else {
				error("Expect number, '1step', or identifier ; receive " + fLexer.peek());
			}
		}
		
		return expr;
	}
	
	public SVExpr event_expression() throws SVParseException {
		if (fLexer.peekOperator("(")) {
			fLexer.eatToken();
			SVParenExpr expr = new SVParenExpr(event_expression());
			fLexer.readOperator(")");
			return expr;
		} else {
			SVExpr ret = null;
			if (fLexer.peekKeyword("posedge", "negedge", "edge")) {
				ret = new SVUnaryExpr(fLexer.eatToken(), expression());
				if (fLexer.peekKeyword("iff")) {
					fLexer.eatToken();
					ret = new SVBinaryExpr(ret, "iff", expression());
				}
			} else {
				ret = expression();
				if (fLexer.peekOperator("iff")) {
					fLexer.eatToken();
					ret = new SVBinaryExpr(ret, "iff", expression());
				}
			}
			
			if (fLexer.peekKeyword("or")) {
				fLexer.eatToken();
				ret = new SVBinaryExpr(ret, "or", event_expression());
			} else if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
				ret = new SVBinaryExpr(ret, ",", event_expression());
			}
			
			return ret;
		}
	}
	
	public SVExpr variable_lvalue() throws SVParseException {
		SVExpr lvalue;
		if (fLexer.peekOperator("{")) {
			SVConcatenationExpr ret = new SVConcatenationExpr();
			// {variable_lvalue, variable_lvalue, ...}
			fLexer.eatToken();
			while (fLexer.peek() != null) {
				ret.getElements().add(variable_lvalue());
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
			fLexer.readOperator("}");
			lvalue = ret;
		} else {
			lvalue = unaryExpression();
		}
		
		return lvalue;
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
		fLexer.init(new ISVParser() {
			
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

					if (!fLexer.peekString() && !fLexer.peekNumber()) {
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
	
	// constraint sc_mode_dist_c {sc_mode dist { 0 := 6, [1:2] := 2, [3:5] :/ 2};}
	
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
		
		if (fLexer.peekOperator(SVKeywords.fAssignmentOps)) {
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
		SVExpr right;
		readOperator(":");
		if (fLexer.peekOperator("$")) {
			fLexer.eatToken();
			right = new SVRangeDollarBoundExpr();
		} else {
			right = expression();
		}
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
		debug("--> conditionalAndExpression()");
		SVExpr a = inclusiveOrExpression();
		
		while (peekOperator("&&")) {
			eatToken();
			a = new SVBinaryExpr(a, "&&", inclusiveOrExpression());
		}
		debug("<-- conditionalAndExpression()");
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
			fLexer.eatToken();
			fLexer.readOperator("{");
			
			if (fLexer.peekOperator("}")) {
				// empty_queue: '{}
				fLexer.eatToken();
				return new SVConcatenationExpr();
			} else {
				SVExpr expr1 = expression();

				if (fLexer.peekOperator("{")) {
					// repetition
					SVAssignmentPatternRepeatExpr ret = new SVAssignmentPatternRepeatExpr(expr1);

					fLexer.eatToken(); // {
					while (true) {
						SVExpr expr = expression();

						ret.getPatternList().add(expr);

						if (fLexer.peekOperator(",")) {
							fLexer.eatToken();
						} else {
							break;
						}
					}
					fLexer.readOperator("}");
					ret_top = ret;
				} else {
					SVAssignmentPatternExpr ret = new SVAssignmentPatternExpr();
					ret.getPatternList().add(expr1);

					while (fLexer.peekOperator(",")) {
						fLexer.eatToken();
						SVExpr expr = expression();

						ret.getPatternList().add(expr);
					}
					ret_top = ret;
				}
				fLexer.readOperator("}");

				return ret_top;
			}
		}
		
		SVExpr a = primary();
		
		if (fLexer.peekOperator("'")) {
			fLexer.eatToken();
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
			if (fLexer.isNumber() || fLexer.isIdentifier() ||
					peekOperator("(", "~", "!") ||
					peekKeyword("this", "super", "new")) {
				ret = new SVCastExpr(a, unaryExpression());
			} else {
				ret = new SVParenExpr(a);
			}
		} else {
			// TODO: must finish and figure out what's going on
			fLexer.peek();
			if (fLexer.isNumber()) {
				ret = new SVLiteralExpr(readNumber());
			} else if (fLexer.peekString()) {
				ret = new SVStringExpr(fLexer.eatToken());
			} else if (fLexer.peekKeyword("null")) {
				fLexer.eatToken();
				ret = new SVNullLiteralExpr();
			} else if (fLexer.isIdentifier() || 
					SVKeywords.isBuiltInType(fLexer.peek()) ||
					fLexer.peekKeyword("new")) {
				debug("  primary \"" + fLexer.getImage() + "\" is identifier or built-in type");
				String id = fLexer.eatToken();
				
				if (peekOperator("(")) {
					if (id.equals("randomize")) {
						return randomize_call(null);
					} else {
						return tf_args_call(null, id);
					}
				} else if (id.equals("new")) {
					return ctor_call();
				} else if (peekKeyword("with")) {
					return tf_noargs_with_call(null, id);
				} else {
					ret = new SVIdentifierExpr(id);
					debug("  after id-read: " + peek());
				}
			} else if (fLexer.peekOperator("{")) {
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
				error("Unexpected token in primary: \"" + fLexer.getImage() + "\"");
			}
		}
		
		debug("<-- primary() " + ret);
		return ret;
	}
	
	private SVExpr concatenation_or_repetition() throws SVParseException {
		debug("--> concatenation_or_repetition()");
		readOperator("{");
		if (peekOperator("}")) {
			// empty_queue
			eatToken();
			debug("<-- concatenation_or_repetition()");
			return new SVConcatenationExpr();
		} else {
			SVExpr expr = expression();

			if (fLexer.peekOperator("{")) {
				fLexer.eatToken();
				// repetition
				SVAssignmentPatternRepeatExpr ret = new SVAssignmentPatternRepeatExpr(expr);

				ret.getPatternList().add(expression());

				while (fLexer.peekOperator(",")) {
					fLexer.eatToken();
					ret.getPatternList().add(expression());
				}
				fLexer.readOperator("}"); // end of inner expression
				fLexer.readOperator("}");
				return ret;
			} else {
				SVConcatenationExpr ret = new SVConcatenationExpr();
				ret.getElements().add(expr);

				while (fLexer.peekOperator(",")) {
					fLexer.eatToken();
					ret.getElements().add(expression());
				}

				fLexer.readOperator("}");

				debug("<-- concatenation_or_repetition()");
				return ret;
			}
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
			if (peekOperator(".")) {
				// named argument
				eatToken();
				SVNamedArgExpr arg_expr = new SVNamedArgExpr();
				String name = readIdentifier();
				arg_expr.setArgName(name);
				readOperator("(");
				arg_expr.setExpr(expression());
				readOperator(")");
				arguments.add(arg_expr);
			} else if (peekOperator(",")) {
				// default value for this parameter
				arguments.add(new SVLiteralExpr(""));
			} else {
				arguments.add(expression());
			}
			
			if (peekOperator(",")) {
				eatToken();
			} else {
				break;
			}
		}
		return arguments.toArray(new SVExpr[arguments.size()]);
	}
	
	public SVExpr selector(SVExpr expr) throws SVParseException {
		if (peekOperator(".", "::")) {
			String q = eatToken();
			
			fLexer.peek();
			if (fLexer.isIdentifier() || peekKeyword("new", "super", "this")) {
				String id = fLexer.eatToken();
				
				if (peekOperator("(")) {
					if (id.equals("randomize")) {
						return randomize_call(expr);
					} else {
						return tf_args_call(expr, id);
					}
				} else if (peekKeyword("with")) {
					return tf_noargs_with_call(expr, id);
				}
				// '.' identifier
				return new SVFieldAccessExpr(expr, (q.equals("::")), id);
			}
		}
		// TODO: Seems redundant
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
			String id;
			if (peekKeyword("new", "super", "this")) {
				id = fLexer.eatToken();
			} else {
				id = readIdentifier();
			}
			
			if (!peekOperator("(")) {
				// '.' super '.' identifier
				return new SVQualifiedSuperFieldRefExpr(expr, id);
			}
		}
		// END: Seems redundant
		
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
		
		error("Unexpected token \"" + fLexer.getImage() + "\"");
		return null; // unreachable, since error always throws an exception
	}
	
	private SVRandomizeCallExpr randomize_call(SVExpr target) throws SVParseException {
		SVRandomizeCallExpr rand_call = new SVRandomizeCallExpr(target, "randomize", arguments());
		
		if (fLexer.peekKeyword("with")) {
			fLexer.eatToken();
			// constraint block
			rand_call.setWithBlock(fParsers.constraintParser().constraint_set(true));
		}
		return rand_call;
	}
	
	private SVTFCallExpr tf_args_call(SVExpr target, String id) throws SVParseException {
		SVTFCallExpr tf = new SVTFCallExpr(target, id, arguments());
		
		if (fLexer.peekKeyword("with")) {
			fLexer.eatToken();
			fLexer.readOperator("(");
			tf.setWithExpr(expression());
			fLexer.readOperator(")");
		}
		
		return tf;
	}
	
	private SVTFCallExpr tf_noargs_with_call(SVExpr target, String id) throws SVParseException {
		SVTFCallExpr tf = new SVTFCallExpr(target, id, null);
		
		if (fLexer.peekKeyword("with")) {
			fLexer.eatToken();
			fLexer.readOperator("(");
			tf.setWithExpr(expression());
			fLexer.readOperator(")");
		}
		
		return tf; 
	}
	
	private SVCtorExpr ctor_call() throws SVParseException {
		SVCtorExpr ctor = new SVCtorExpr();
		if (fLexer.peekOperator("[")) {
			// array constructor
			fLexer.readOperator("[");
			ctor.setDim(expression());
			fLexer.readOperator("]");
		}
		if (fLexer.peekOperator("(")) {
			ctor.setArgs(arguments());
		}
		
		return ctor;
	}
	
	private String peek() throws SVParseException {
		return fLexer.peek();
	}

	private boolean peekOperator(String ... ops) throws SVParseException {
		return fLexer.peekOperator(ops);
	}
	
	private String readOperator(String ... ops) throws SVParseException {
		return fLexer.readOperator(ops);
	}
	
	private boolean peekKeyword(String ... kw) throws SVParseException {
		return fLexer.peekKeyword(kw);
	}
	
	private String readKeyword(String ... kw) throws SVParseException {
		return fLexer.readKeyword(kw);
	}
	
	private String readIdentifier() throws SVParseException {
		return fLexer.readId();
	}
	
	private String readNumber() throws SVParseException {
		return fLexer.readNumber();
	}
	
	private String eatToken() {
		return fLexer.eatToken();
	}
}
