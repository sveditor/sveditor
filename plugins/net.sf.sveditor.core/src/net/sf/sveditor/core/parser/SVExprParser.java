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
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVCoverageExpr;
import net.sf.sveditor.core.db.expr.SVDBArrayAccessExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignmentPatternExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignmentPatternRepeatExpr;
import net.sf.sveditor.core.db.expr.SVDBAssociativeArrayElemAssignExpr;
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
import net.sf.sveditor.core.db.expr.SVDBNameMappedExpr;
import net.sf.sveditor.core.db.expr.SVDBNamedArgExpr;
import net.sf.sveditor.core.db.expr.SVDBNullExpr;
import net.sf.sveditor.core.db.expr.SVDBParamIdExpr;
import net.sf.sveditor.core.db.expr.SVDBParenExpr;
import net.sf.sveditor.core.db.expr.SVDBRandomizeCallExpr;
import net.sf.sveditor.core.db.expr.SVDBRangeDollarBoundExpr;
import net.sf.sveditor.core.db.expr.SVDBRangeExpr;
import net.sf.sveditor.core.db.expr.SVDBStringExpr;
import net.sf.sveditor.core.db.expr.SVDBTFCallExpr;
import net.sf.sveditor.core.db.expr.SVDBTypeExpr;
import net.sf.sveditor.core.db.expr.SVDBUnaryExpr;
import net.sf.sveditor.core.db.expr.SVExprParseException;
import net.sf.sveditor.core.scanner.SVKeywords;
import net.sf.sveditor.core.scanutils.ITextScanner;

public class SVExprParser extends SVParserBase {
//	private SVExprDump						fExprDump;
//	private boolean							fDebugEn = false;
	public static boolean					fUseFullExprParser = true;
	private boolean							fEventExpr;
	private boolean							fEnableNameMappedPrimary = false;
	
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
		debug("--> delay_expr - " + fLexer.peek());
		
		fLexer.readOperator("#");
		
		if (fLexer.peekOperator("(")) {
			fLexer.eatToken();
			expr = fParsers.exprParser().expression();
			fLexer.readOperator(")");
		} else {
			if (fLexer.peekNumber()) {
				debug("  isNumber - " + fLexer.peek());
				expr = new SVDBLiteralExpr(fLexer.eatToken());
			} else if (fLexer.peekOperator("1step")) {
				expr = new SVDBLiteralExpr(fLexer.eatToken());
			} else if (fLexer.peekId()) {
				debug("  isExpression");
				expr = expression();
			} else {
				error("Expect number, '1step', or identifier ; receive " + fLexer.peek());
			}
		}
		
		debug("<-- delay_expr - " + fLexer.peek());
		return expr;
	}
	
	public SVDBExpr datatype_or_expression() throws SVParseException {
		if (fLexer.peekKeyword("virtual","const") || fLexer.peekKeyword(SVKeywords.fBuiltinTypes)) {
			// Know this is a type
			SVDBTypeExpr expr = new SVDBTypeExpr();
			expr.setLocation(fLexer.getStartLocation());
			
			SVDBTypeInfo info = fParsers.dataTypeParser().data_type(0);
			expr.setTypeInfo(info);
			
			return expr;
		} else {
			return expression();
		}
		
	}
	
	public SVDBExpr event_expression() throws SVParseException {
		debug("--> event_expression()");
		fEventExpr = true;
		try {
			return expression();
			
			/*
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
					debug("    event 'or' expression");
					fLexer.eatToken();
					ret = new SVDBBinaryExpr(ret, "or", event_expression());
				} else if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
					ret = new SVDBBinaryExpr(ret, ",", event_expression());
				}

				debug("<-- event_expression()");
				return ret;
			}
			 */
		} finally {
			fEventExpr = false;
		}
	}
	
	public SVDBExpr variable_lvalue() throws SVParseException {
		SVDBExpr lvalue;
		debug("--> variable_lvalue - " + fLexer.peek());
		if (fLexer.peekOperator("{")) {
			lvalue = concatenation_or_repetition();
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
		
		if (fEventExpr && fLexer.peekKeyword("iff")) {
			fLexer.eatToken();
			expr = new SVDBBinaryExpr(expr, "iff", expression());
		}
		
		if (fEventExpr && fLexer.peekOperator(",")) {
			fLexer.eatToken();
			expr = new SVDBBinaryExpr(expr, ",", expression());
		}
//		debug("<-- expression() " + expr);
		
		return expr; 
	}
	
	public SVDBExpr hierarchical_identifier() throws SVParseException {
		String id = fLexer.readId();
		
		if (fLexer.peekOperator(".")) {
			return new SVDBFieldAccessExpr(new SVDBIdentifierExpr(id), false, 
					hierarchical_identifier_int());
		} else {
			return new SVDBIdentifierExpr(id);
		}
	}
	
	private SVDBExpr hierarchical_identifier_int() throws SVParseException {
		fLexer.readOperator(".");

		String id = fLexer.readId();
		
		if (fLexer.peekOperator(".")) {
			return new SVDBFieldAccessExpr(new SVDBIdentifierExpr(id), 
					false, hierarchical_identifier_int());
		} else {
			return new SVDBIdentifierExpr(id);
		}
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
		
		while (peekOperator("||") || (fEventExpr && fLexer.peekKeyword("or"))) {
			String op = eatToken();
			a = new SVDBBinaryExpr(a, op, conditionalAndExpression());
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
		debug("--> inclusiveOrExpression");
		SVDBExpr a = exclusiveOrExpression();
		
		while (peekOperator("|")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "|", exclusiveOrExpression());
		}
		
		debug("<-- inclusiveOrExpression");
		return a;
	}
	
	public SVDBExpr exclusiveOrExpression() throws SVParseException {
		debug("--> exclusiveOrExpression");
		SVDBExpr a = andExpression();
		
		while (peekOperator("^")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "^", andExpression());
		}
		
		debug("<-- exclusiveOrExpression");
		return a;
	}
	
	public SVDBExpr andExpression() throws SVParseException {
		debug("--> andExpression");
		SVDBExpr a = equalityExpression();
		
		while (peekOperator("&")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "&", equalityExpression());
		}
		
		debug("<-- andExpression");
		return a;
	}
	
	public SVDBExpr equalityExpression() throws SVParseException {
		debug("--> equalityExpression");
		SVDBExpr a = relationalExpression();
		
		while (peekOperator("==", "!=", "===", "!==", "==?", "!=?")) {
			a = new SVDBBinaryExpr(a, readOperator(), relationalExpression());
		}
		
		debug("<-- equalityExpression");
		return a;
	}
	
	public SVDBExpr relationalExpression() throws SVParseException {
		debug("--> relationalExpression");
		SVDBExpr a = shiftExpression();
		
		while (peekOperator("<", ">", "<=", ">=")) {
			a = new SVDBBinaryExpr(a, readOperator(), shiftExpression());
		}
		
		debug("<-- relationalExpression");
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
		
		while (peekOperator("*", "/", "%", "**")) {
			a = new SVDBBinaryExpr(a, readOperator(), unaryExpression());
		}
		return a;
	}
	
	public SVDBExpr unaryExpression() throws SVParseException {
		debug("--> unaryExpression");
		if (peekOperator("++", "--")) {
			return new SVDBIncDecExpr(readOperator(), unaryExpression());
		} else if (fEventExpr && fLexer.peekKeyword("posedge", "negedge", "edge")) {
			SVDBExpr ret = new SVDBUnaryExpr(fLexer.eatToken(), expression());
			if (fLexer.peekKeyword("iff")) {
				fLexer.eatToken();
				ret = new SVDBBinaryExpr(ret, "iff", expression());
			}
			return ret;
		}
		if (peekOperator("+", "-", "~", "!", "&", "~&", "|", "~|", "^", "~^", "^~")) {
			String op = readOperator();
			SVDBUnaryExpr ret = new SVDBUnaryExpr(op, unaryExpression());
			
			debug("<-- unaryExpression " + op);
			return ret; 
		} else if (peekOperator("'")) {
			SVDBAssignmentPatternExpr ret_top = null;
			fLexer.eatToken();
			fLexer.readOperator("{");
			
			if (fLexer.peekOperator("}")) {
				// empty_queue: '{}
				fLexer.eatToken();
				return new SVDBConcatenationExpr();
			} else {
				// This could be an associative-array initialization statement
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
				} else if (fLexer.peekOperator(":")) {
					// associative-array assignment
					SVDBAssignmentPatternExpr ret = new SVDBAssignmentPatternExpr();
					SVDBAssociativeArrayElemAssignExpr assign;
					
					while (fLexer.peek() != null) {
						assign = new SVDBAssociativeArrayElemAssignExpr();
						if (expr1 == null) {
							expr1 = expression();
						}
						assign.setKey(expr1);
						fLexer.readOperator(":");
						assign.setValue(expression());
						ret.getPatternList().add(assign);
						
						if (fLexer.peekOperator(",")) {
							fLexer.eatToken();
						} else {
							break;
						}
						expr1 = null;
					}
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

				debug("<-- unaryExpression");
				return ret_top;
			}
		}
		
		SVDBExpr a = primary();
		
		if (fLexer.peekOperator("'")) {
			fLexer.eatToken();
			// MSB: new cast expression
			a = new SVDBCastExpr(a, expression());
		}
		
		debug("peek: " + fLexer.peek());
		while (peekOperator("::", ".", "[")) {
			a = selector(a);
		}
		
		while (peekOperator("++", "--")) {
			a = new SVDBIncDecExpr(readOperator(), a);
		}
		
		return a;
	}
	
	public SVDBExpr primary() throws SVParseException {
		debug("--> primary() - " + fLexer.peek());
		SVDBExpr ret = null;
		
		if (peekOperator("(")) {
			debug("  Found paren in primary");
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
				debug("-- primary is a number");
				ret = new SVDBLiteralExpr(readNumber());
			} else if (fLexer.peekOperator("$")) {
				fLexer.eatToken();
				return new SVDBRangeDollarBoundExpr();
			} else if (fLexer.peekString()) {
				debug("-- primary is a string");
				ret = new SVDBStringExpr(fLexer.eatToken());
			} else if (fLexer.peekKeyword("null")) {
				debug("-- primary is 'null'");
				fLexer.eatToken();
				ret = new SVDBNullExpr();
			} else if (fLexer.isIdentifier() || 
					SVKeywords.isBuiltInType(fLexer.peek()) ||
					fLexer.peekKeyword("new","default")) {
				debug("  primary \"" + fLexer.getImage() + "\" is identifier or built-in type");
				String id = fLexer.eatToken();
				
				if (fLexer.peekOperator("(*")) {
					fParsers.attrParser().parse(null);
				}
				
				if (peekOperator("#")) {
					// Parameterized identifier
					ret = new SVDBParamIdExpr(id);
					fLexer.eatToken(); // #
					fLexer.readOperator("(");
					while (fLexer.peek() != null) {
						((SVDBParamIdExpr)ret).addParamExpr(datatype_or_expression());
						if (fLexer.peekOperator(",")) {
							fLexer.eatToken();
						} else {
							break;
						}
					}
					fLexer.readOperator(")");
				} else if (peekOperator("(")) {
					if (id.equals("randomize")) {
						return randomize_call(null);
					} else {
						return tf_args_call(null, id);
					}
				} else if (id.equals("new")) {
					return ctor_call();
				} else if (peekKeyword("with")) {
					return tf_noargs_with_call(null, id);
				} else if (fLexer.peekKeyword(SVKeywords.fBuiltinDeclTypes)) {
					fLexer.startCapture();
					fLexer.eatToken();
					if (fLexer.peekKeyword("signed","unsigned")) {
						fLexer.eatToken();
					}
					return new SVDBIdentifierExpr(fLexer.endCapture());
				} else {
					// ID or 'default'
					if (fEnableNameMappedPrimary && fLexer.peekOperator(":")) {
						fLexer.eatToken();
						ret = new SVDBNameMappedExpr(id, expression());
					} else {
						ret = new SVDBIdentifierExpr(id);
					}
					debug("  after id-read: " + peek());
				}
			} else if (fLexer.peekOperator("{")) {
				// concatenation
				ret = concatenation_or_repetition();
			} else if (peekKeyword("this")) {
				eatToken();
				return new SVDBIdentifierExpr("this");
			} else if (peekKeyword("super")) {
				eatToken();
				return new SVDBIdentifierExpr("super");
			} else if (peekKeyword("void")) {
				eatToken();
				return new SVDBIdentifierExpr("void");
			} else {
				error("Unexpected token in primary: \"" + fLexer.getImage() + "\"");
			}
		}
		
		debug("<-- primary() ");
		return ret;
	}
	
	private SVDBExpr concatenation_or_repetition() throws SVParseException {
		SVDBExpr expr = null;
		debug("--> concatenation_or_repetition()");
		readOperator("{");
		if (peekOperator("}")) {
			// empty_queue
			eatToken();
			debug("<-- concatenation_or_repetition()");
			return new SVDBConcatenationExpr();
		} else if (peekOperator("<<", ">>")) {
			debug("streaming operator");
			// TODO: preserve this portion of expression
			fLexer.eatToken();
			
			if (fLexer.peekKeyword(SVKeywords.fBuiltinTypes)) {
				expr = new SVDBTypeExpr(fParsers.dataTypeParser().data_type(0));
			} else if (!fLexer.peekOperator("{")) {
				expr = new SVDBLiteralExpr(eatToken());
			}
			
			debug("post-datatype: " + fLexer.peek());
			
			fLexer.readOperator("{");
			while (fLexer.peek() != null) {
				expression();
				
				debug("pre-with: " + fLexer.peek());
				if (fLexer.peekKeyword("with")) {
					fLexer.eatToken();
					fLexer.readOperator("[");
					expression();
					if (fLexer.peekOperator(":", "+:", "-:")) {
						fLexer.eatToken();
						expression();
					}
					fLexer.readOperator("]");
				}
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
			fLexer.readOperator("}");
			fLexer.readOperator("}");
				
			return new SVDBConcatenationExpr();
		} else {
			try {
				fEnableNameMappedPrimary = true;
				SVDBExpr expr0 = expression();

				// concatenation or repetition
				if (fLexer.peekOperator("{")) {
					debug("repetition");
					fLexer.eatToken();
					// repetition
					SVDBAssignmentPatternRepeatExpr ret = new SVDBAssignmentPatternRepeatExpr(expr);
					ret.setRepeatExpr(expr0);

					while (fLexer.peek() != null) {
						ret.getPatternList().add(expression());
						if (fLexer.peekOperator(",")) {
							fLexer.eatToken();
						} else {
							break;
						}
					}
					fLexer.readOperator("}"); // end of inner expression
					fLexer.readOperator("}");
					return ret;
				} else {
					debug("concatenation");
					SVDBConcatenationExpr ret = new SVDBConcatenationExpr();
					ret.getElements().add(expr0);

					while (fLexer.peekOperator(",")) {
						fLexer.eatToken();
						ret.getElements().add(expression());
					}

					fLexer.readOperator("}");

					debug("<-- concatenation_or_repetition()");
					return ret;
				}
			} finally {
				fEnableNameMappedPrimary = false;
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
	
	private List<SVDBExpr>  argumentList() throws SVParseException {
		List<SVDBExpr> arguments = new ArrayList<SVDBExpr>();
		
		for (;;) {
			if (peekOperator(".")) {
				// named argument
				eatToken();
				SVDBNamedArgExpr arg_expr = new SVDBNamedArgExpr();
				String name = readIdentifier();
				arg_expr.setArgName(name);
				readOperator("(");
				if (fLexer.peekOperator(")")) {
					// empty argument specifier
					arg_expr.setExpr(new SVDBLiteralExpr(""));
				} else {
					arg_expr.setExpr(expression());
				}
				readOperator(")");
				arguments.add(arg_expr);
			} else if (peekOperator(",", ")")) {
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
				
				if (fLexer.peekOperator("(*")) {
					fParsers.attrParser().parse(null);
				}
				
				if (peekOperator("(")) {
					if (id.equals("randomize")) {
						return randomize_call(expr);
					} else {
						return tf_args_call(expr, id);
					}
				} else if (peekKeyword("with")) {
					debug("triggering off with");
					return tf_noargs_with_call(expr, id);
				}
				// '.' identifier
				return new SVDBFieldAccessExpr(expr, (q.equals("::")), 
						new SVDBIdentifierExpr(id));
			}
		}
		/*
		// TODO: Seems redundant
		if (peekKeyword("this")) {
			// '.' 'this'
			eatToken();
			return new SVDBIdentifierExpr("this");
		}
		if (peekKeyword("super")) {
			eatToken();
			
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
		 */
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
		
		// TODO:
		if (fLexer.peekKeyword("with")) {
			fLexer.eatToken();
			if (fLexer.peekOperator("[")) {
				fLexer.readOperator("[");
				tf.setWithExpr(expression());
				if (fLexer.peekOperator(":", "+:","-:")) {
					fLexer.eatToken();
					expression();
				}
				fLexer.readOperator("]");
			} else {
				fLexer.readOperator("(");
				tf.setWithExpr(expression());
				fLexer.readOperator(")");
			}
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
