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
import java.util.Stack;

import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVCoverageExpr;
import net.sf.sveditor.core.db.expr.SVDBArrayAccessExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignmentPatternExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignmentPatternRepeatExpr;
import net.sf.sveditor.core.db.expr.SVDBBinaryExpr;
import net.sf.sveditor.core.db.expr.SVDBCastExpr;
import net.sf.sveditor.core.db.expr.SVDBClockingEventExpr;
import net.sf.sveditor.core.db.expr.SVDBClockingEventExpr.ClockingEventType;
import net.sf.sveditor.core.db.expr.SVDBConcatenationExpr;
import net.sf.sveditor.core.db.expr.SVDBCondExpr;
import net.sf.sveditor.core.db.expr.SVDBCoverBinsExpr;
import net.sf.sveditor.core.db.expr.SVDBCoverpointExpr;
import net.sf.sveditor.core.db.expr.SVDBCtorExpr;
import net.sf.sveditor.core.db.expr.SVDBCycleDelayExpr;
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
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVExprParser extends SVParserBase {
//	private SVExprDump						fExprDump;
//	private boolean							fDebugEn = false;
	public static boolean					fUseFullExprParser = true;
	private Stack<Boolean>					fEventExpr;
	private Stack<Boolean>					fAssertionExpr;
	private boolean							fEnableNameMappedPrimary = false;
	
	public SVExprParser(ISVParser parser) {
		super(parser);
		fAssertionExpr = new Stack<Boolean>();
		fAssertionExpr.push(false);
		fEventExpr = new Stack<Boolean>();
		fEventExpr.push(false);
//		fExprDump = new SVExprDump(System.out);
	}
	
	///////////////////////////////////////////////////////////////////////////////////////////////
	// This routine is used to parse an "@(xxx)"  
	// Formats supported are:
	// @*
	// @(*)
	// @(some_series_of_events)
	// @some event
	// Before calling fLexer.peekOperator("@") to prevent an exception
	///////////////////////////////////////////////////////////////////////////////////////////////
	public SVDBClockingEventExpr clocking_event() throws SVParseException {
		SVDBClockingEventExpr expr = new SVDBClockingEventExpr();
		fLexer.readOperator("@");
		// Check if there is an open brace - kill it if so
		if (fLexer.peekOperator("(")) {
			SVDBParenExpr p = new SVDBParenExpr();
			p.setLocation(fLexer.getStartLocation());
			fLexer.eatToken();
			// Handle @(*)
			if (fLexer.peekOperator("*"))  {
				// swallow the *
				fLexer.readOperator("*");
				expr.setClockingEventType(ClockingEventType.Any);
				// TODO: How do I set the expression?
			}
			// grab the event expression
			else  {
				expr.setClockingEventType(ClockingEventType.Expr);
				p.setExpr(event_expression());
				expr.setExpr(p);
			}
			fLexer.readOperator(")");
		}
		// handle @*
		else  if (fLexer.peekOperator("*"))  {
			expr.setClockingEventType(ClockingEventType.Any);
			// swallow the *
			fLexer.readOperator("*");
			// TODO: How do I set the expression?
//			expr.setExpr(idExpr());
		}
		// Handle @ some_event_name
		else  {
			expr.setClockingEventType(ClockingEventType.Expr);
			expr.setExpr(idExpr());
		}
		
		return expr;
	}
	
	public SVDBExpr cycle_delay() throws SVParseException {
		SVDBCycleDelayExpr expr = new SVDBCycleDelayExpr();
		expr.setLocation(fLexer.getStartLocation());
		fLexer.readOperator("##");
		if (fLexer.peekNumber()) {
			expr.setExpr(literalExpr());
		} else if (fLexer.peekOperator("(")) {
			fLexer.readOperator("(");
			expr.setExpr(expression());
			fLexer.readOperator(")");
		} else {
			expr.setExpr(idExpr());
		}
		return expr;
	}
	
	// Checks for following:
	// #(delay)
	// #(rise_delay,fall_delay)
	// #(min_rise_delay:typ_rise_delay:max_rise_delay,min_fall_delay:typ_fall_delay:max_fall_delay)
	// #(min_delay:typ_delay:max_delay)
	// There are two delay types, delay 2 and delay 3.  The difference between them is that delay 2 has Rise and Fall, where delay 3 has rise, fall and tristate times
	public SVDBExpr delay_expr(int max_delays) throws SVParseException {
		SVDBExpr expr = null;
		if (fDebugEn) {debug("--> delay_expr - " + fLexer.peek());}

		if ((max_delays != 2) && (max_delays != 3))  {
			error ("delay_expr - should have either 2 or 3 as arguments");
		}
		fLexer.readOperator("#");
		if (fLexer.peekOperator("(")) {
			fLexer.eatToken();
			expr = fParsers.exprParser().expression();
			// TODO: save expression
			// Check for (min:typ:max) type of layout 
			if (fLexer.peekOperator(":"))  {
				fLexer.readOperator(":");
				expr = fParsers.exprParser().expression();
				// This should be another :, not going to test... going to assume that the parser will detect that this isn't a token
				fLexer.readOperator(":");
				expr = fParsers.exprParser().expression();
			}
			for (int i = 2; i<=max_delays; i++)  {
				// Check for "," which implies a falling edge delay
				if (fLexer.peekOperator(","))  {
					fLexer.eatToken();
					expr = fParsers.exprParser().expression();
					// TODO: save expression
					// Check for (min:typ:max) type of layout 
					if (fLexer.peekOperator(":"))  {
						fLexer.readOperator(":");
						expr = fParsers.exprParser().expression();
						// This should be another :, not going to test... going to assume that the parser will detect that this isn't a token
						fLexer.readOperator(":");
						expr = fParsers.exprParser().expression();
					}
				}
			}
			fLexer.readOperator(")");
		} else {
			if (fLexer.peekNumber()) {
				if (fDebugEn) {debug("  isNumber - " + fLexer.peek());}
				expr = new SVDBLiteralExpr(fLexer.eatToken());
			} else if (fLexer.peekOperator("1step")) {
				expr = new SVDBLiteralExpr(fLexer.eatToken());
			} else if (fLexer.peekId()) {
				if (fDebugEn) {debug("  isIdExpression");}
				expr = hierarchical_identifier(); // idExpr();
			} else {
				error("Expect number, '1step', or identifier ; receive " + fLexer.peek());
			}
		}
		
		if (fDebugEn) {debug("<-- delay_expr - " + fLexer.peek());}
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
	
	public SVDBExpr assert_expression() throws SVParseException {
		fAssertionExpr.push(true);
		fEventExpr.push(true);
		try {
			return expression();
		} finally {
			fAssertionExpr.pop();
			fEventExpr.pop();
		}
	}
	
	public SVDBExpr event_expression() throws SVParseException {
		if (fDebugEn) {debug("--> event_expression()");}
		fEventExpr.push(true);
		try {
			return expression();
		} finally {
			fEventExpr.pop();
		}
	}
	
	public SVDBExpr variable_lvalue() throws SVParseException {
		SVDBExpr lvalue;
		if (fDebugEn) {debug("--> variable_lvalue - " + fLexer.peek());}
		if (fLexer.peekOperator("{")) {
			lvalue = concatenation_or_repetition();
		} else {
			lvalue = unaryExpression();
		}
		
		if (fDebugEn) {debug("<-- variable_lvalue - " + fLexer.peek());}
		return lvalue;
	}
	
	public SVDBExpr const_or_range_expression() throws SVParseException {
		if (fDebugEn) {debug("--> const_or_range_expression - " + fLexer.peek());}
		SVDBExpr expr = expression();
		if (fLexer.peekOperator(":")) {
			fLexer.eatToken();
			expr = new SVDBRangeExpr(expr, expression());
		}
		if (fDebugEn) {debug("<-- const_or_range_expression - " + fLexer.peek());}
		return expr;
	}

	/**
	 * Expression := AssignmentExpression
	 * @param tok
	 * @return
	 * @throws SVParseException
	 */
	public SVDBExpr expression() throws SVParseException {
		SVDBExpr expr = null;
		if (fDebugEn) {debug("--> expression() " + fLexer.peek());}
		expr = assignmentExpression();
		
		if (fEventExpr.peek() && fLexer.peekKeyword("iff")) {
			fLexer.eatToken();
			expr = new SVDBBinaryExpr(expr, "iff", expression());
		}
		
		if (fEventExpr.peek() && fLexer.peekOperator(",")) {
			fLexer.eatToken();
			expr = new SVDBBinaryExpr(expr, ",", expression());
		}
		if (fDebugEn) {debug("<-- expression() after=" + fLexer.peek());}
		
		return expr; 
	}
	
	public SVDBExpr hierarchical_identifier() throws SVParseException {
		if (fDebugEn) {debug("--> hierarchical_identifier - " + fLexer.peek());}
		SVDBExpr ret;
		String id = fLexer.readId();
		
		if (fLexer.peekOperator(".","::")) {
			ret = new SVDBFieldAccessExpr(new SVDBIdentifierExpr(id), false, 
					hierarchical_identifier_int());
		} else {
			ret = new SVDBIdentifierExpr(id);
		}
		if (fDebugEn) {debug("<-- hierarchical_identifier - " + fLexer.peek());}
		return ret;
	}
	
	private SVDBExpr hierarchical_identifier_int() throws SVParseException {
		fLexer.readOperator(".","::");

		String id = fLexer.readId();
		
		if (fLexer.peekOperator(".","::")) {
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
		if (fDebugEn) {debug("--> assignmentExpression()");}
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

		if (fDebugEn) {debug("<-- assignmentExpression() " + fLexer.peek());}
		return a;
	}
	
	public void open_range_list(List<SVDBExpr> list) throws SVParseException {
		if (fDebugEn) {debug("--> open_range_list - " + fLexer.peek());}
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
		if (fDebugEn) {debug("<-- open_range_list - " + fLexer.peek());}
	}
	
	public SVDBRangeExpr parse_range() throws SVParseException {
		if (fDebugEn) {debug("--> parse_range - " + fLexer.peek());}
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
		
		if (fDebugEn) {debug("<-- parse_range - " + fLexer.peek());}
		return new SVDBRangeExpr(left, right);
	}
	
	/**
	 * conditionalExpression ::=
	 *     conditionalOrExpression [ '?' Expression ':' ConditionalExpression]
	 * @return
	 * @throws SVParseException
	 */
	public SVDBExpr conditionalExpression() throws SVParseException {
		if (fDebugEn) {debug("--> conditionalExpression()");}
		SVDBExpr a = conditionalOrExpression();
		
		if (fDebugEn) {debug("    post-conditionalOrExpression: " + fLexer.peek());}
		
		if (fLexer.peekOperator("?")) {
			eatToken();

			SVDBExpr lhs = a;
			SVDBExpr mhs = expression();
			readOperator(":");

			SVDBExpr rhs = conditionalExpression();
			a = new SVDBCondExpr(lhs, mhs, rhs);
		}
		if (fDebugEn) {debug("<-- conditionalExpression() ");}
		return a;
	}
	
	/**
	 * conditionalOrExpression ::=
	 * 		conditionalAndExpression { '||' conditionalAndExpression }
	 * @return
	 * @throws SVParseException
	 */
	public SVDBExpr conditionalOrExpression() throws SVParseException {
		if (fDebugEn) {debug("--> conditionalOrExpression()");}
		SVDBExpr a = conditionalAndExpression();
		
		while (peekOperator("||") || (fEventExpr.peek() && fLexer.peekKeyword("or"))) {
			String op = eatToken();
			a = new SVDBBinaryExpr(a, op, conditionalAndExpression());
		}
		
		if (fDebugEn) {debug("<-- conditionalOrExpression() ");}
		return a;
	}
	
	/**
	 * conditionalAndExpression ::=
	 * 	inclusiveOrExpression { '&&' inclusiveOrExpression }
	 * @return
	 * @throws SVParseException
	 */
	public SVDBExpr conditionalAndExpression() throws SVParseException {
		if (fDebugEn) {debug("--> conditionalAndExpression()");}
		SVDBExpr a = inclusiveOrExpression();
		
		while (peekOperator("&&")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "&&", inclusiveOrExpression());
		}
		if (fDebugEn) {debug("<-- conditionalAndExpression()");}
		return a;
	}
	
	public SVDBExpr inclusiveOrExpression() throws SVParseException {
		if (fDebugEn) {debug("--> inclusiveOrExpression");}
		SVDBExpr a = exclusiveOrExpression();
		
		while (peekOperator("|")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "|", exclusiveOrExpression());
		}
		
		if (fDebugEn) {debug("<-- inclusiveOrExpression");}
		return a;
	}
	
	public SVDBExpr exclusiveOrExpression() throws SVParseException {
		if (fDebugEn) {debug("--> exclusiveOrExpression");}
		SVDBExpr a = exclusiveNorExpression1();
		
		while (peekOperator("^")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "^", exclusiveNorExpression1());
		}
		
		if (fDebugEn) {debug("<-- exclusiveOrExpression");}
		return a;
	}
	
	public SVDBExpr exclusiveNorExpression1() throws SVParseException {
		if (fDebugEn) {debug("--> exclusiveNorExpression1");}
		SVDBExpr a = exclusiveNorExpression2();
		
		while (peekOperator("^~")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "^~", exclusiveNorExpression2());
		}
		
		if (fDebugEn) {debug("<-- exclusiveNorExpression1");}
		return a;
	}
	
	public SVDBExpr exclusiveNorExpression2() throws SVParseException {
		if (fDebugEn) {debug("--> exclusiveNorExpression2");}
		SVDBExpr a = andExpression();
		
		while (peekOperator("~^")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "~^", andExpression());
		}
		
		if (fDebugEn) {debug("<-- exclusiveNorExpression2");}
		return a;
	}
	
	public SVDBExpr andExpression() throws SVParseException {
		if (fDebugEn) {debug("--> andExpression");}
		SVDBExpr a = equalityExpression();
		
		while (peekOperator("&")) {
			eatToken();
			a = new SVDBBinaryExpr(a, "&", equalityExpression());
		}
		
		if (fDebugEn) {debug("<-- andExpression");}
		return a;
	}
	
	public SVDBExpr equalityExpression() throws SVParseException {
		if (fDebugEn) {debug("--> equalityExpression");}
		SVDBExpr a = relationalExpression();
		
		while (peekOperator("==", "!=", "===", "!==", "==?", "!=?")) {
			a = new SVDBBinaryExpr(a, readOperator(), relationalExpression());
		}
		
		if (fDebugEn) {debug("<-- equalityExpression");}
		return a;
	}
	
	public SVDBExpr relationalExpression() throws SVParseException {
		if (fDebugEn) {debug("--> relationalExpression");}
		SVDBExpr a = shiftExpression();
		
		while (peekOperator("<", ">", "<=", ">=")) {
			a = new SVDBBinaryExpr(a, readOperator(), shiftExpression());
		}
		
		if (fDebugEn) {debug("<-- relationalExpression");}
		return a;
	}
	
	public SVDBExpr shiftExpression() throws SVParseException {
		if (fDebugEn) {debug("--> shiftExpression");}
		SVDBExpr a = additiveExpression();
		
		while (peekOperator("<<", "<<<", ">>", ">>>")) {
			a = new SVDBBinaryExpr(a, readOperator(), additiveExpression());
		}
		
		if (fDebugEn) {debug("<-- shiftExpression");}
		return a;
	}
	
	public SVDBExpr additiveExpression() throws SVParseException {
		if (fDebugEn) {debug("--> additiveExpression");}
		SVDBExpr a = multiplicativeExpression();
		
		while (peekOperator("+", "-")) {
			a = new SVDBBinaryExpr(a, readOperator(), multiplicativeExpression());
		}
		if (fDebugEn) {debug("<-- additiveExpression");}
		return a;
	}
	
	public SVDBExpr multiplicativeExpression() throws SVParseException {
		if (fDebugEn) {debug("--> multiplicativeExpression " + fLexer.peek());}
		SVDBExpr a = unaryExpression();
		
		while (peekOperator("*", "/", "%", "**")) {
			a = new SVDBBinaryExpr(a, readOperator(), unaryExpression());
		}
		if (fDebugEn) {debug("<-- multiplicativeExpression");}
		return a;
	}
	
	public SVDBExpr unaryExpression() throws SVParseException {
		if (fDebugEn) {debug("--> unaryExpression " + fLexer.peek());}
		if (peekOperator("++", "--")) {
			return new SVDBIncDecExpr(readOperator(), unaryExpression());
		} else if (fEventExpr.peek() && fLexer.peekKeyword("posedge", "negedge", "edge")) {
			SVDBExpr ret = new SVDBUnaryExpr(fLexer.eatToken(), expression());
			if (fLexer.peekKeyword("iff")) {
				fLexer.eatToken();
				ret = new SVDBBinaryExpr(ret, "iff", expression());
			}
			return ret;
		}
		if (peekOperator("+", "-", "~", "!", "&", "~&", "|", "~|", "^", "~^", "^~") ||
				(fAssertionExpr.peek() && peekOperator("*"))) {
			String op = readOperator();
			SVDBUnaryExpr ret = new SVDBUnaryExpr(op, unaryExpression());
			
			if (fDebugEn) {debug("<-- unaryExpression " + op);}
			return ret; 
		} else if (peekOperator("'")) {
			return assignment_pattern_expr();
		}
		
		SVDBExpr a = primary();
		
		if (fDebugEn) {debug("unaryExpr -- peek: " + fLexer.peek());}
		while (peekOperator("::", ".", "[")) {
			SVToken t = fLexer.consumeToken();
			// Don't move forward if this is likely to be an assertion sequence
			if (fAssertionExpr.peek()) {
				if (!fLexer.peekOperator()) {
					fLexer.ungetToken(t);
					a = selector(a);
				} else {
					fLexer.ungetToken(t);
					break;
				}
			} else {
				fLexer.ungetToken(t);
				a = selector(a);
			}
		}

		if (fLexer.peekOperator("'")) {
			SVToken tok = fLexer.consumeToken();
			if (fLexer.peekOperator("{")) {
				fLexer.ungetToken(tok);
				a = assignment_pattern_expr();
			} else {
				fLexer.ungetToken(tok);
				if (fDebugEn) {debug("    castExpr");}
				fLexer.eatToken();
				// MSB: new cast expression
				a = new SVDBCastExpr(a, expression());
			}
		}

		while (peekOperator("++", "--")) {
			a = new SVDBIncDecExpr(readOperator(), a);
		}
		
		return a;
	}
	
	private SVDBExpr assignment_pattern_expr() throws SVParseException {
		SVDBExpr ret_top;
		fLexer.readOperator("'");
		fLexer.readOperator("{");
		if (fDebugEn) {debug("    assignmentPattern");}
		
		if (fLexer.peekOperator("}")) {
			// empty_queue: '{}
			fLexer.eatToken();
			ret_top = new SVDBConcatenationExpr();
		} else {

			try {
				fEnableNameMappedPrimary = true;
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
				} /*else if (fLexer.peekOperator(":")) {
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
				} */ else {
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
			} finally {
				fEnableNameMappedPrimary = false;
			}
		}
		return ret_top;
	}
	
	public SVDBExpr primary() throws SVParseException {
		if (fDebugEn) {debug("--> primary() - " + fLexer.peek());}
		SVDBExpr ret = null;
		
		if (peekOperator("(")) {
			if (fDebugEn) {debug("  Found paren in primary");}
			eatToken();
			
			// if (isType) {
			// TODO
			//
			
			SVDBExpr a = expression();
			
			// TODO: save expression
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				SVDBExpr expr = fParsers.exprParser().expression();
				if (fLexer.peekOperator(":")) {
					fLexer.eatToken();
					expr = fParsers.exprParser().expression();
				}
			}
			
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
				if (fDebugEn) {debug("-- primary is a number");}
				ret = new SVDBLiteralExpr(readNumber());
			} else if (fLexer.peekOperator("$")) {
				fLexer.eatToken();
				ret = new SVDBRangeDollarBoundExpr();
			} else if (fLexer.peekString()) {
				if (fDebugEn) {debug("-- primary is a string");}
				SVToken tmp = fLexer.consumeToken();
				if (fEnableNameMappedPrimary && fLexer.peekOperator(":")) {
					fLexer.eatToken();
					ret = new SVDBNameMappedExpr(tmp.getImage(), expression());
				} else {
					ret = new SVDBStringExpr(tmp.getImage());
				}
			} else if (fLexer.peekKeyword("null")) {
				if (fDebugEn) {debug("-- primary is 'null'");}
				fLexer.eatToken();
				ret = new SVDBNullExpr();
			} else if (fLexer.isIdentifier() || 
					SVKeywords.isBuiltInType(fLexer.peek()) ||
					fLexer.peekKeyword("new","default","local")) {
				if (fDebugEn) {
					debug("  primary \"" + fLexer.getImage() + "\" is identifier or built-in type");
				}
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
				} else if (fLexer.peekOperator("(") || fLexer.peekKeyword("with")) {
					if (id.equals("randomize")) {
						ret = randomize_call(null);
					} else if (fLexer.peekOperator("(")) {
						ret = tf_args_call(null, id);
					} else {
						ret = tf_noargs_with_call(null, id);
					}
				} else if (id.equals("new")) {
					ret = ctor_call();
				} else if (fLexer.peekKeyword(SVKeywords.fBuiltinDeclTypes)) {
					fLexer.startCapture();
					fLexer.eatToken();
					if (fLexer.peekKeyword("signed","unsigned")) {
						fLexer.eatToken();
					}
					ret = new SVDBIdentifierExpr(fLexer.endCapture());
				} else {
					// ID or 'default'
					if (fEnableNameMappedPrimary && fLexer.peekOperator(":")) {
						fLexer.eatToken();
						if (fDebugEn) {debug("    nameMappedExpr");}
						ret = new SVDBNameMappedExpr(id, expression());
					} else {
						ret = new SVDBIdentifierExpr(id);
					}
					if (fDebugEn) {debug("  after id-read: " + peek());}
				}
			} else if (fLexer.peekOperator("{")) {
				// concatenation
				ret = concatenation_or_repetition();
			} else if (peekKeyword("this")) {
				eatToken();
				ret = new SVDBIdentifierExpr("this");
			} else if (peekKeyword("super")) {
				eatToken();
				ret = new SVDBIdentifierExpr("super");
			} else if (peekKeyword("void")) {
				eatToken();
				ret = new SVDBIdentifierExpr("void");
			} else if (fEventExpr.peek() && fLexer.peekOperator("@")) {
				ret = clocking_event();
			} else if (fEventExpr.peek() && fLexer.peekOperator("##")) {
				ret = cycle_delay();
			} else {
				error("Unexpected token in primary: \"" + fLexer.getImage() + "\"");
			}
		}
		
		if (fDebugEn) {debug("<-- primary() ");}
		return ret;
	}
	
	private SVDBExpr concatenation_or_repetition() throws SVParseException {
		SVDBExpr expr = null;
		if (fDebugEn) {debug("--> concatenation_or_repetition()");}
		readOperator("{");
		if (peekOperator("}")) {
			// empty_queue
			eatToken();
			expr = new SVDBConcatenationExpr();
		} else if (peekOperator("<<", ">>")) {
			if (fDebugEn) {debug("streaming operator");}
			// TODO: preserve this portion of expression
			fLexer.eatToken();
			
			if (fLexer.peekKeyword(SVKeywords.fBuiltinTypes)) {
				expr = new SVDBTypeExpr(fParsers.dataTypeParser().data_type(0));
			} else if (!fLexer.peekOperator("{")) {
				expr = new SVDBLiteralExpr(eatToken());
			}
			
			if (fDebugEn) {debug("post-datatype: " + fLexer.peek());}
			
			fLexer.readOperator("{");
			while (fLexer.peek() != null) {
				expression();
				
				if (fDebugEn) {debug("pre-with: " + fLexer.peek());}
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
				
			expr = new SVDBConcatenationExpr();
		} else {
			try {
//				fEnableNameMappedPrimary = true;
				SVDBExpr expr0 = expression();

				// concatenation or repetition
				if (fLexer.peekOperator("{")) {
					if (fDebugEn) {debug("repetition");}
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
					expr = ret;
				} else {
					if (fDebugEn) {debug("concatenation");}
					SVDBConcatenationExpr ret = new SVDBConcatenationExpr();
					ret.getElements().add(expr0);

					while (fLexer.peekOperator(",")) {
						fLexer.eatToken();
						ret.getElements().add(expression());
					}

					fLexer.readOperator("}");

					expr = ret;
				}
			} finally {
//				fEnableNameMappedPrimary = false;
			}
		}
		if (fDebugEn) {debug("<-- concatenation_or_repetition()");}
		return expr;
	}
	
	public List<SVDBExpr> arguments() throws SVParseException {
		if (fDebugEn) {debug("--> arguments()");}
		readOperator("(");
		
		if (peekOperator(")")) {
			eatToken();
			return new ArrayList<SVDBExpr>();
		}
		
		List<SVDBExpr> arguments = argumentList();
		
		readOperator(")");
		
		if (fDebugEn) {debug("<-- arguments()");}
		return arguments;
	}
	
	private List<SVDBExpr>  argumentList() throws SVParseException {
		List<SVDBExpr> arguments = new ArrayList<SVDBExpr>();
		if (fDebugEn) {debug("--> argumentList()");}
		
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
		
		if (fDebugEn) {debug("<-- argumentList()");}
		return arguments;
	}
	
	public SVDBExpr selector(SVDBExpr expr) throws SVParseException {
		if (fDebugEn) {debug("--> selector()");}
		if (peekOperator(".", "::")) {
			String q = eatToken();
			
			fLexer.peek();
			if (fLexer.isIdentifier() || peekKeyword("new", "super", "this")) {
				String id = fLexer.eatToken();
				
				if (fLexer.peekOperator("(*")) {
					fParsers.attrParser().parse(null);
				}
				
				if (fLexer.peekOperator("(") || fLexer.peekKeyword("with")) {
					if (id.equals("randomize")) {
						return randomize_call(expr);
					} else if (fLexer.peekOperator("(")){
						return tf_args_call(expr, id);
					} else {
						return tf_noargs_with_call(expr, id);
					}
				}
				// '.' identifier
				if (fDebugEn) {debug("<-- selector()");}
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
		// TODO: keyword class`
		
		if (peekOperator("[")) {
			if (fDebugEn) {debug("primary() -- operator " + fLexer.peek());}
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
			if (fDebugEn) {debug("<-- selector()");}
			return new SVDBArrayAccessExpr(expr, low, high);
		}
		
		error("Unexpected token \"" + fLexer.getImage() + "\"");
		return null; // unreachable, since error always throws an exception
	}
	
	private SVDBRandomizeCallExpr randomize_call(SVDBExpr target) throws SVParseException {
		List<SVDBExpr> arguments = null;
		SVDBRandomizeCallExpr rand_call = null;
		
		// Body of a randomize() call should not user assertion semantics
		fAssertionExpr.push(false);
		fEventExpr.push(false);
		try {
			if (fLexer.peekOperator("(")) {
				arguments = arguments();
			}

			rand_call = new SVDBRandomizeCallExpr(target, "randomize", arguments);

			if (fLexer.peekKeyword("with")) {
				fLexer.eatToken();
				// constraint block
				rand_call.setWithBlock(fParsers.constraintParser().constraint_set(true));
			}
		} finally {
			fAssertionExpr.pop();
			fEventExpr.pop();
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
		if (fDebugEn) {
			debug("--> ctor_call()");
		}
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
		
		if (fDebugEn) {
			debug("--> ctor_call()");
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
	
	public SVDBLiteralExpr literalExpr() throws SVParseException {
		SVDBLocation start = fLexer.getStartLocation();
		SVDBLiteralExpr ret = new SVDBLiteralExpr(fLexer.readNumber());
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
