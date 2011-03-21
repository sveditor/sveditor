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

import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.expr.SVCoverageExpr;
import net.sf.sveditor.core.db.expr.SVDBArrayAccessExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignmentPatternExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignmentPatternRepeatExpr;
import net.sf.sveditor.core.db.expr.SVDBBinaryExpr;
import net.sf.sveditor.core.db.expr.SVDBCastExpr;
import net.sf.sveditor.core.db.expr.SVDBClockingEventExpr;
import net.sf.sveditor.core.db.expr.SVDBConcatenationExpr;
import net.sf.sveditor.core.db.expr.SVDBCondExpr;
import net.sf.sveditor.core.db.expr.SVDBCoverBinsExpr;
import net.sf.sveditor.core.db.expr.SVDBCoverpointExpr;
import net.sf.sveditor.core.db.expr.SVDBCtorExpr;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBFieldAccessExpr;
import net.sf.sveditor.core.db.expr.SVDBIdentifierExpr;
import net.sf.sveditor.core.db.expr.SVDBIncDecExpr;
import net.sf.sveditor.core.db.expr.SVDBInsideExpr;
import net.sf.sveditor.core.db.expr.SVDBLiteralExpr;
import net.sf.sveditor.core.db.expr.SVDBNamedArgExpr;
import net.sf.sveditor.core.db.expr.SVDBNullExpr;
import net.sf.sveditor.core.db.expr.SVDBParenExpr;
import net.sf.sveditor.core.db.expr.SVDBQualifiedSuperFieldRefExpr;
import net.sf.sveditor.core.db.expr.SVDBQualifiedThisRefExpr;
import net.sf.sveditor.core.db.expr.SVDBRandomizeCallExpr;
import net.sf.sveditor.core.db.expr.SVDBRangeDollarBoundExpr;
import net.sf.sveditor.core.db.expr.SVDBRangeExpr;
import net.sf.sveditor.core.db.expr.SVDBStringExpr;
import net.sf.sveditor.core.db.expr.SVDBSuperExpr;
import net.sf.sveditor.core.db.expr.SVDBTFCallExpr;
import net.sf.sveditor.core.db.expr.SVDBThisExpr;
import net.sf.sveditor.core.db.expr.SVDBUnaryExpr;
import net.sf.sveditor.core.db.expr.SVExprParseException;
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
	
	public SVDBClockingEventExpr clocking_event() throws SVParseException {
		SVDBClockingEventExpr expr = new SVDBClockingEventExpr();
		fLexer.readOperator("@");
		if (fLexer.peekOperator("(")) {
			expr.setExpr(event_expression());
		} else {
			expr.setExpr(idExpr());
		}
		
		return expr;
	}
	
	public SVDBExpr delay_expr() throws SVParseException {
		SVDBExpr expr = null;
		
		fLexer.readOperator("#");
		
		if (fLexer.peekOperator("(")) {
			fLexer.eatToken();
			expr = fParsers.exprParser().expression();
			fLexer.readOperator(")");
		} else {
			if (fLexer.peekNumber()) {
				expr = new SVDBLiteralExpr(fLexer.eatToken());
			} else if (fLexer.peekOperator("1step")) {
				expr = new SVDBLiteralExpr(fLexer.eatToken());
			} else if (fLexer.peekId()) {
				expr = new SVDBLiteralExpr(fLexer.eatToken());
			} else {
				error("Expect number, '1step', or identifier ; receive " + fLexer.peek());
			}
		}
		
		return expr;
	}
	
	public SVDBExpr event_expression() throws SVParseException {
		if (fLexer.peekOperator("(")) {
			fLexer.eatToken();
			SVDBParenExpr expr = new SVDBParenExpr(event_expression());
			fLexer.readOperator(")");
			return expr;
		} else {
			SVDBExpr ret = null;
			if (fLexer.peekKeyword("posedge", "negedge", "edge")) {
				ret = new SVDBUnaryExpr(fLexer.eatToken(), expression());
				if (fLexer.peekKeyword("iff")) {
					fLexer.eatToken();
					ret = new SVDBBinaryExpr(ret, "iff", expression());
				}
			} else {
				ret = expression();
				if (fLexer.peekOperator("iff")) {
					fLexer.eatToken();
					ret = new SVDBBinaryExpr(ret, "iff", expression());
				}
			}
			
			if (fLexer.peekKeyword("or")) {
				fLexer.eatToken();
				ret = new SVDBBinaryExpr(ret, "or", event_expression());
			} else if (fLexer.peekOperator(",")) {
				fLexer.eatToken();
				ret = new SVDBBinaryExpr(ret, ",", event_expression());
			}
			
			return ret;
		}
	}
	
	public SVDBExpr variable_lvalue() throws SVParseException {
		SVDBExpr lvalue;
		if (fLexer.peekOperator("{")) {
			SVDBConcatenationExpr ret = new SVDBConcatenationExpr();
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
	public SVDBExpr expression() throws SVParseException {
		SVDBExpr expr = null;
//		debug("--> expression()");
		expr = assignmentExpression();
//		debug("<-- expression() " + expr);
		
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
	public SVDBExpr parse_expression(ITextScanner in) throws SVExprParseException {
//		init(in);
		SVDBExpr expr = null;
		
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
	public void coverpoint_target(SVDBCoverpointExpr coverpoint) throws SVParseException {
		
		try {
			SVDBExpr target = expression();

			coverpoint.setTarget(target);

			if (peekKeyword("iff")) {
				eatToken();
				readOperator("(");
				SVDBExpr iff_expr = expression();
				readOperator(")");

				coverpoint.setIFFExpr(iff_expr);
			}
		} catch (EOFException e) {
			e.printStackTrace();
			// Ignore
		}
	}
	
	public void coverpoint_body(SVDBCoverpointExpr coverpoint) throws SVParseException {
		
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

					SVDBCoverBinsExpr bins = new SVDBCoverBinsExpr(bins_id, bins_kw);

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
	public SVDBExpr assignmentExpression() throws SVParseException {
		debug("--> assignmentExpression()");
		SVDBExpr a = conditionalExpression();
		
		if (fLexer.peekOperator(SVKeywords.fAssignmentOps)) {
			String op = readOperator();
			SVDBExpr rhs = assignmentExpression();
			a = new SVDBAssignExpr(a, op, rhs);
		} else if (peekKeyword("inside")) {
			eatToken();
			SVDBInsideExpr inside = new SVDBInsideExpr(a);
			
			open_range_list(inside.getValueRangeList());
			
			a = inside;
		}

		debug("<-- assignmentExpression() ");
		return a;
	}
	
	public void open_range_list(List<SVDBExpr> list) throws SVParseException {
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
	
	public SVDBRangeExpr parse_range() throws SVParseException {
		readOperator("[");
		SVDBExpr left = expression();
		SVDBExpr right;
		readOperator(":");
		if (fLexer.peekOperator("$")) {
			fLexer.eatToken();
			right = new SVDBRangeDollarBoundExpr();
		} else {
			right = expression();
		}
		readOperator("]");
		
		return new SVDBRangeExpr(left, right);
	}
	
	/**
	 * conditionalExpression ::=
	 *     conditionalOrExpression [ '?' Expression ':' ConditionalExpression]
	 * @return
	 * @throws SVParseException
	 */
	public SVDBExpr conditionalExpression() throws SVParseException {
		debug("--> conditionalExpression()");
		SVDBExpr a = conditionalOrExpression();
		
		if (!peekOperator("?")) return a;
		eatToken();
		
		SVDBExpr lhs = a;
		SVDBExpr mhs = expression();
		readOperator(":");
		
		SVDBExpr rhs = conditionalExpression();
		a = new SVDBCondExpr(lhs, mhs, rhs);
		debug("<-- conditionalExpression() ");
		return a;
	}
	
	/**
	 * conditionalOrExpression ::=
	 * 		conditionalAndExpression { '||' conditionalAndExpression }
	 * @return
	 * @throws SVParseException
	 */
	public SVDBExpr conditionalOrExpression() throws SVParseException {
		debug("--> conditionalOrExpression()");
		SVDBExpr a = conditionalAndExpression();
		
		while (peekOperator("||")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "||", conditionalAndExpression());
		}
		
		debug("<-- conditionalOrExpression() ");
		return a;
	}
	
	/**
	 * conditionalAndExpression ::=
	 * 	inclusiveOrExpression { '&&' inclusiveOrExpression }
	 * @return
	 * @throws SVParseException
	 */
	public SVDBExpr conditionalAndExpression() throws SVParseException {
		debug("--> conditionalAndExpression()");
		SVDBExpr a = inclusiveOrExpression();
		
		while (peekOperator("&&")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "&&", inclusiveOrExpression());
		}
		debug("<-- conditionalAndExpression()");
		return a;
	}
	
	public SVDBExpr inclusiveOrExpression() throws SVParseException {
		SVDBExpr a = exclusiveOrExpression();
		
		while (peekOperator("|")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "|", exclusiveOrExpression());
		}
		
		return a;
	}
	
	public SVDBExpr exclusiveOrExpression() throws SVParseException {
		SVDBExpr a = andExpression();
		
		while (peekOperator("^")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "^", andExpression());
		}
		
		return a;
	}
	
	public SVDBExpr andExpression() throws SVParseException {
		SVDBExpr a = equalityExpression();
		
		while (peekOperator("&")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "&", equalityExpression());
		}
		
		return a;
	}
	
	public SVDBExpr equalityExpression() throws SVParseException {
		SVDBExpr a = relationalExpression();
		
		while (peekOperator("==", "!=", "===", "!==", "==?", "!=?")) {
			a = new SVDBBinaryExpr(a, readOperator(), relationalExpression());
		}
		
		return a;
	}
	
	public SVDBExpr relationalExpression() throws SVParseException {
		SVDBExpr a = shiftExpression();
		
		while (peekOperator("<", ">", "<=", ">=")) {
			a = new SVDBBinaryExpr(a, readOperator(), shiftExpression());
		}
		
		return a;
	}
	
	public SVDBExpr shiftExpression() throws SVParseException {
		SVDBExpr a = additiveExpression();
		
		while (peekOperator("<<", ">>", ">>>")) {
			a = new SVDBBinaryExpr(a, readOperator(), additiveExpression());
		}
		
		return a;
	}
	
	public SVDBExpr additiveExpression() throws SVParseException {
		SVDBExpr a = multiplicativeExpression();
		
		while (peekOperator("+", "-")) {
			a = new SVDBBinaryExpr(a, readOperator(), multiplicativeExpression());
		}
		return a;
	}
	
	public SVDBExpr multiplicativeExpression() throws SVParseException {
		SVDBExpr a = unaryExpression();
		
		while (peekOperator("*", "/", "%")) {
			a = new SVDBBinaryExpr(a, readOperator(), unaryExpression());
		}
		return a;
	}
	
	public SVDBExpr unaryExpression() throws SVParseException {
		if (peekOperator("++", "--")) {
			return new SVDBIncDecExpr(readOperator(), unaryExpression());
		}
		if (peekOperator("+", "-", "~", "!", "&", "~&", "|", "~|", "^", "~^", "^~")) {
			return new SVDBUnaryExpr(readOperator(), unaryExpression());
		} else if (peekOperator("'")) {
			SVDBAssignmentPatternExpr ret_top = null;
			fLexer.eatToken();
			fLexer.readOperator("{");
			
			if (fLexer.peekOperator("}")) {
				// empty_queue: '{}
				fLexer.eatToken();
				return new SVDBConcatenationExpr();
			} else {
				SVDBExpr expr1 = expression();

				if (fLexer.peekOperator("{")) {
					// repetition
					SVDBAssignmentPatternRepeatExpr ret = new SVDBAssignmentPatternRepeatExpr(expr1);

					fLexer.eatToken(); // {
					while (true) {
						SVDBExpr expr = expression();

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
					SVDBAssignmentPatternExpr ret = new SVDBAssignmentPatternExpr();
					ret.getPatternList().add(expr1);

					while (fLexer.peekOperator(",")) {
						fLexer.eatToken();
						SVDBExpr expr = expression();

						ret.getPatternList().add(expr);
					}
					ret_top = ret;
				}
				fLexer.readOperator("}");

				return ret_top;
			}
		}
		
		SVDBExpr a = primary();
		
		if (fLexer.peekOperator("'")) {
			fLexer.eatToken();
			// MSB: new cast expression
			a = new SVDBCastExpr(a, expression());
		}
		
		while (peekOperator("::", ".", "[")) {
			a = selector(a);
		}
		
		while (peekOperator("++", "--")) {
			a = new SVDBIncDecExpr(readOperator(), a);
		}
		
		return a;
	}
	
	public SVDBExpr primary() throws SVParseException {
		debug("--> primary()");
		SVDBExpr ret = null;
		
		if (peekOperator("(")) {
			eatToken();
			
			// if (isType) {
			// TODO
			//
			
			SVDBExpr a = expression();
			readOperator(")");
			
			// cast
			// '(' expression() ')' unaryExpression
			peek();
			if (fLexer.isNumber() || fLexer.isIdentifier() ||
					peekOperator("(", "~", "!") ||
					peekKeyword("this", "super", "new")) {
				ret = new SVDBCastExpr(a, unaryExpression());
			} else {
				ret = new SVDBParenExpr(a);
			}
		} else {
			// TODO: must finish and figure out what's going on
			fLexer.peek();
			if (fLexer.isNumber()) {
				ret = new SVDBLiteralExpr(readNumber());
			} else if (fLexer.peekString()) {
				ret = new SVDBStringExpr(fLexer.eatToken());
			} else if (fLexer.peekKeyword("null")) {
				fLexer.eatToken();
				ret = new SVDBNullExpr();
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
					ret = new SVDBIdentifierExpr(id);
					debug("  after id-read: " + peek());
				}
			} else if (fLexer.peekOperator("{")) {
				// concatenation
				ret = concatenation_or_repetition();
			} else if (peekKeyword("this")) {
				eatToken();
				return new SVDBThisExpr();
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
				return new SVDBSuperExpr();
				// error("Unhandled primary 'super'");
			} else if (peekKeyword("void")) {
				eatToken();
			} else {
				error("Unexpected token in primary: \"" + fLexer.getImage() + "\"");
			}
		}
		
		debug("<-- primary() ");
		return ret;
	}
	
	private SVDBExpr concatenation_or_repetition() throws SVParseException {
		debug("--> concatenation_or_repetition()");
		readOperator("{");
		if (peekOperator("}")) {
			// empty_queue
			eatToken();
			debug("<-- concatenation_or_repetition()");
			return new SVDBConcatenationExpr();
		} else {
			SVDBExpr expr = expression();

			if (fLexer.peekOperator("{")) {
				fLexer.eatToken();
				// repetition
				SVDBAssignmentPatternRepeatExpr ret = new SVDBAssignmentPatternRepeatExpr(expr);

				ret.getPatternList().add(expression());

				while (fLexer.peekOperator(",")) {
					fLexer.eatToken();
					ret.getPatternList().add(expression());
				}
				fLexer.readOperator("}"); // end of inner expression
				fLexer.readOperator("}");
				return ret;
			} else {
				SVDBConcatenationExpr ret = new SVDBConcatenationExpr();
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
	
	public List<SVDBExpr> arguments() throws SVParseException {
		readOperator("(");
		
		if (peekOperator(")")) {
			eatToken();
			return new ArrayList<SVDBExpr>();
		}
		
		List<SVDBExpr> arguments = argumentList();
		
		readOperator(")");
		
		return arguments;
	}
	
	public List<SVDBExpr>  argumentList() throws SVParseException {
		List<SVDBExpr> arguments = new ArrayList<SVDBExpr>();
		
		for (;;) {
			if (peekOperator(".")) {
				// named argument
				eatToken();
				SVDBNamedArgExpr arg_expr = new SVDBNamedArgExpr();
				String name = readIdentifier();
				arg_expr.setArgName(name);
				readOperator("(");
				arg_expr.setExpr(expression());
				readOperator(")");
				arguments.add(arg_expr);
			} else if (peekOperator(",")) {
				// default value for this parameter
				arguments.add(new SVDBLiteralExpr(""));
			} else {
				arguments.add(expression());
			}
			
			if (peekOperator(",")) {
				eatToken();
			} else {
				break;
			}
		}
		return arguments;
	}
	
	public SVDBExpr selector(SVDBExpr expr) throws SVParseException {
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
				return new SVDBFieldAccessExpr(expr, (q.equals("::")), id);
			}
		}
		// TODO: Seems redundant
		if (peekKeyword("this")) {
			// '.' 'this'
			eatToken();
			return new SVDBQualifiedThisRefExpr(expr);
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
				return new SVDBQualifiedSuperFieldRefExpr(expr, id);
			}
		}
		// END: Seems redundant
		
		// TODO: keyword new
		// TODO: keyword class
		
		if (peekOperator("[")) {
			// '[' expression ']'
			eatToken();
			SVDBExpr low = expression();
			SVDBExpr high = null;
			
			// TODO: should probably preserve array-bounds method
			if (peekOperator(":", "+:", "-:")) {
				eatToken();
				high = expression();
			}
			
			readOperator("]");
			if (expr == null) {
				error("array expr == null");
			}
			return new SVDBArrayAccessExpr(expr, low, high);
		}
		
		error("Unexpected token \"" + fLexer.getImage() + "\"");
		return null; // unreachable, since error always throws an exception
	}
	
	private SVDBRandomizeCallExpr randomize_call(SVDBExpr target) throws SVParseException {
		SVDBRandomizeCallExpr rand_call = new SVDBRandomizeCallExpr(target, "randomize", arguments());
		
		if (fLexer.peekKeyword("with")) {
			fLexer.eatToken();
			// constraint block
			rand_call.setWithBlock(fParsers.constraintParser().constraint_set(true));
		}
		return rand_call;
	}
	
	private SVDBTFCallExpr tf_args_call(SVDBExpr target, String id) throws SVParseException {
		SVDBTFCallExpr tf = new SVDBTFCallExpr(target, id, arguments());
		
		if (fLexer.peekKeyword("with")) {
			fLexer.eatToken();
			fLexer.readOperator("(");
			tf.setWithExpr(expression());
			fLexer.readOperator(")");
		}
		
		return tf;
	}
	
	private SVDBTFCallExpr tf_noargs_with_call(SVDBExpr target, String id) throws SVParseException {
		SVDBTFCallExpr tf = new SVDBTFCallExpr(target, id, null);
		
		if (fLexer.peekKeyword("with")) {
			fLexer.eatToken();
			fLexer.readOperator("(");
			tf.setWithExpr(expression());
			fLexer.readOperator(")");
		}
		
		return tf; 
	}
	
	private SVDBCtorExpr ctor_call() throws SVParseException {
		SVDBCtorExpr ctor = new SVDBCtorExpr();
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
	
	public SVDBIdentifierExpr idExpr() throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		SVDBIdentifierExpr ret = new SVDBIdentifierExpr(fLexer.readId());
		ret.setLocation(start);
		
		return ret;
	}
	
	private String readNumber() throws SVParseException {
		return fLexer.readNumber();
	}
	
	private String eatToken() {
		return fLexer.eatToken();
	}
}
