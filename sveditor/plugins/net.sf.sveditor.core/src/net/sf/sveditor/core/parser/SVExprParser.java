/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package net.sf.sveditor.core.parser;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import net.sf.sveditor.core.db.SVDBParamValueAssignList;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.expr.SVCoverageExpr;
import net.sf.sveditor.core.db.expr.SVDBArrayAccessExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignmentPatternExpr;
import net.sf.sveditor.core.db.expr.SVDBAssignmentPatternRepeatExpr;
import net.sf.sveditor.core.db.expr.SVDBAssociativeArrayAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBAssociativeArrayElemAssignExpr;
import net.sf.sveditor.core.db.expr.SVDBBinaryExpr;
import net.sf.sveditor.core.db.expr.SVDBCastExpr;
import net.sf.sveditor.core.db.expr.SVDBClockingEventExpr;
import net.sf.sveditor.core.db.expr.SVDBClockingEventExpr.ClockingEventType;
import net.sf.sveditor.core.db.expr.SVDBConcatenationExpr;
import net.sf.sveditor.core.db.expr.SVDBCondExpr;
import net.sf.sveditor.core.db.expr.SVDBCoverBinsExpr;
import net.sf.sveditor.core.db.expr.SVDBCoverpointExpr;
import net.sf.sveditor.core.db.expr.SVDBCtorExpr;
import net.sf.sveditor.core.db.expr.SVDBCtorExpr.CtorType;
import net.sf.sveditor.core.db.expr.SVDBCycleDelayExpr;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBFieldAccessExpr;
import net.sf.sveditor.core.db.expr.SVDBForeachLoopvarExpr;
import net.sf.sveditor.core.db.expr.SVDBIdentifierExpr;
import net.sf.sveditor.core.db.expr.SVDBIncDecExpr;
import net.sf.sveditor.core.db.expr.SVDBInsideExpr;
import net.sf.sveditor.core.db.expr.SVDBLiteralExpr;
import net.sf.sveditor.core.db.expr.SVDBMinTypMaxExpr;
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
import net.sf.sveditor.core.db.stmt.SVDBConstraintDistListStmt;
import net.sf.sveditor.core.parser.SVLexer.Context;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVExprParser extends SVParserBase {
//	private SVExprDump						fExprDump;
//	private boolean							fDebugEn = false;
	public static boolean					fUseFullExprParser = true;
	private Stack<Boolean>					fEventExpr;
	private Stack<Boolean>					fAssertionExpr;
	private Stack<Boolean>					fArglistExpr;
	private Stack<Boolean>					fForeachLoopvarExpr;
	private Stack<Boolean>					fEnableNameMappedPrimary;
	private boolean							fSaveExpr = true;
	private int								fParenLevel = 0;
	
	public SVExprParser(ISVParser parser) {
		super(parser);
		fAssertionExpr = new Stack<Boolean>();
		fAssertionExpr.push(false);
		fEventExpr = new Stack<Boolean>();
		fEventExpr.push(false);
		fArglistExpr = new Stack<Boolean>();
		fArglistExpr.push(false);
		fForeachLoopvarExpr = new Stack<Boolean>();
		fForeachLoopvarExpr.push(false);
		fEnableNameMappedPrimary = new Stack<Boolean>();
		fEnableNameMappedPrimary.push(false);
//		fExprDump = new SVExprDump(System.out);
	}
	
	///////////////////////////////////////////////////////////////////////////////////////////////
	// This routine is used to parse an "@(xxx)"  
	// Formats supported are:
	// @*
	// @(*)
	// @(some_series_of_events)
	// @some event
	// Before calling fLexer.peekOperator(OP.AT) to prevent an exception
	///////////////////////////////////////////////////////////////////////////////////////////////
	public SVDBClockingEventExpr clocking_event() throws SVParseException {
		SVDBClockingEventExpr expr = new SVDBClockingEventExpr();
		fLexer.readOperator(OP.AT);
		// Check if there is an open brace - kill it if so
		if (fLexer.peekOperator(OP.LPAREN)) {
			SVDBParenExpr p = new SVDBParenExpr();
			p.setLocation(fLexer.getStartLocation());
			fLexer.eatToken();
			// Handle @(*)
			if (fLexer.peekOperator(OP.MUL))  {
				// swallow the *
				fLexer.readOperator(OP.MUL);
				expr.setClockingEventType(ClockingEventType.Any);
				// TODO: How do I set the expression?
			}
			// grab the event expression
			else  {
				expr.setClockingEventType(ClockingEventType.Expr);
				p.setExpr(event_expression());
				expr.setExpr(p);
			}
			fLexer.readOperator(OP.RPAREN);
		}
		// handle @*
		else  if (fLexer.peekOperator(OP.MUL))  {
			expr.setClockingEventType(ClockingEventType.Any);
			// swallow the *
			fLexer.readOperator(OP.MUL);
			// TODO: How do I set the expression?
//			expr.setExpr(idExpr());
		}
		// Handle @ some_event_name
		else  {
			expr.setClockingEventType(ClockingEventType.Expr);
//			expr.setExpr(idExpr());
			expr.setExpr(event_expression());
		}
		
		return expr;
	}
	
	private final static Set<OP> fUnaryModulePathOperators;
	private final static Set<OP> fBinaryModulePathOperators;
	static {
		fUnaryModulePathOperators = new HashSet<OP>();
		fUnaryModulePathOperators.add(OP.NOT);
		fUnaryModulePathOperators.add(OP.NEG);
		fUnaryModulePathOperators.add(OP.AND);
		fUnaryModulePathOperators.add(OP.NEG_AND);
		fUnaryModulePathOperators.add(OP.OR);
		fUnaryModulePathOperators.add(OP.NEG_OR);
		fUnaryModulePathOperators.add(OP.XOR);
		fUnaryModulePathOperators.add(OP.NEG_XOR);
		fUnaryModulePathOperators.add(OP.XOR_NEG);
		
		fBinaryModulePathOperators = new HashSet<OP>();
		fBinaryModulePathOperators.add(OP.EQ2);
		fBinaryModulePathOperators.add(OP.NOT_EQ);
		fBinaryModulePathOperators.add(OP.AND2);
		fBinaryModulePathOperators.add(OP.OR2);
		fBinaryModulePathOperators.add(OP.AND);
		fBinaryModulePathOperators.add(OP.OR);
		fBinaryModulePathOperators.add(OP.XOR);
		fBinaryModulePathOperators.add(OP.XOR_NEG);
		fBinaryModulePathOperators.add(OP.NEG_XOR);
	}
	
	public SVDBExpr module_path_expression() throws SVParseException {
		SVDBExpr ret = null;
		if (fDebugEn) {
			debug("--> module_path_expression() " + fLexer.peek());
		}
		
		if (fLexer.peekOperator(OP.LPAREN)) {
			fLexer.readOperator(OP.LPAREN);
			module_path_expression();
			fLexer.readOperator(OP.RPAREN);
		} 
		
		if (fLexer.peekOperator(fUnaryModulePathOperators)) {
			fLexer.eatToken();
			module_path_primary();
		} else {
			module_path_primary();
		}
		
		if (fLexer.peekOperator(fBinaryModulePathOperators)) {
			String op = fLexer.eatTokenR();
			if (fDebugEn) {
				debug("  op=" + op);
			}
			module_path_expression();
		}
	
		if (fDebugEn) {
			debug("<-- module_path_expression() " + fLexer.peek());
		}
		return ret;
	}
	
	private SVDBExpr module_path_primary() throws SVParseException {
		SVDBExpr ret = null;
		if (fLexer.peekNumber()) {
			ret = literalExpr();
		} else if (fLexer.peekId()) {
			// id | function_subroutine_call
			ret = idExpr();
			// TODO: function_subroutine_call
			if (fLexer.peekOperator(OP.LPAREN)) {
				error("function_subroutine_call unsupported");
			} else if (fLexer.peekOperator(OP.LBRACKET)) {
				fLexer.eatToken();
				ret = new SVDBArrayAccessExpr(
						ret, fParsers.exprParser().expression(), null);
				fLexer.readOperator(OP.RBRACKET);
			}
		} else if (fLexer.peekOperator(OP.LBRACE)) {
			error("module_path_concatenation|module_path_multiple_concatenation unsupported");
			// module_path_concatenation | module_path_multiple_concatenation
			fLexer.eatToken(); // {
			if (fLexer.peekOperator(OP.LBRACE)) {
				// module_path_multiple_concatenation
				// TODO:
			} else {
				
			}
		} else if (fLexer.peekOperator(OP.LPAREN)) {
			// module_path_mintypmax_expression
			ret = delay_or_specify_delay_expr(false, 3); 
		} /* else {
			error("Expecting [,{,(,ID,Number ; received " +
					fLexer.peek());
		} */

		return ret;
	}

	
	
	public SVDBExpr cycle_delay() throws SVParseException {
		SVDBCycleDelayExpr expr = new SVDBCycleDelayExpr();
		expr.setLocation(fLexer.getStartLocation());
		fLexer.readOperator(OP.HASH2);
		if (fLexer.peekNumber()) {
			expr.setExpr(literalExpr());
		} else if (fLexer.peekOperator(OP.LPAREN)) {
			fLexer.readOperator(OP.LPAREN);
			expr.setExpr(expression());
			fLexer.readOperator(OP.RPAREN);
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
		return delay_or_specify_delay_expr(true, max_delays);
	}
	
	public SVDBExpr delay_or_specify_delay_expr(boolean delay_expr, int max_delays) throws SVParseException {
		SVDBExpr expr = null;
		if (fDebugEn) {debug("--> delay_expr - " + fLexer.peek());}

		if ((max_delays != 2) && (max_delays != 3))  {
			error ("delay_expr - should have either 2 or 3 as arguments");
		}
		if (delay_expr) {
			fLexer.readOperator(OP.HASH, OP.HASH2);
		}
		if (fLexer.peekOperator(OP.LPAREN)) {
			fLexer.eatToken();
			expr = fParsers.exprParser().expression();
			// TODO: save expression
			// Check for (min:typ:max) type of layout 
			if (fLexer.peekOperator(OP.COLON))  {
				fLexer.readOperator(OP.COLON);
				expr = fParsers.exprParser().expression();
				// This should be another :, not going to test... going to assume that the parser will detect that this isn't a token
				fLexer.readOperator(OP.COLON);
				expr = fParsers.exprParser().expression();
			}
			for (int i = 2; i<=max_delays; i++)  {
				// Check for "," which implies a falling edge delay
				if (fLexer.peekOperator(OP.COMMA))  {
					fLexer.eatToken();
					expr = fParsers.exprParser().expression();
					// TODO: save expression
					// Check for (min:typ:max) type of layout 
					if (fLexer.peekOperator(OP.COLON))  {
						fLexer.readOperator(OP.COLON);
						expr = fParsers.exprParser().expression();
						// This should be another :, not going to test... going to assume that the parser will detect that this isn't a token
						fLexer.readOperator(OP.COLON);
						expr = fParsers.exprParser().expression();
					}
				}
			}
			fLexer.readOperator(OP.RPAREN);
		} else {
			expr = delay_value();
		}
		
		if (fDebugEn) {debug("<-- delay_expr - " + fLexer.peek());}
		return expr;
	}
	
	public SVDBExpr path_delay_value() throws SVParseException {
		boolean in_parens = fLexer.peekOperator(OP.LPAREN);
		
		if (in_parens) {
			fLexer.eatToken();
		}

		while (fLexer.peek() != null) {
			expression();
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}

		
		if (in_parens) {
			fLexer.readOperator(OP.RPAREN);
		}
	
		// TODO:
		return null;
	}
	
	private SVDBExpr delay_value() throws SVParseException {
		SVDBExpr ret = null;
		if (fDebugEn) {debug("--> delay_value() : " + fLexer.peek());}
		
		if (fLexer.peekNumber()) {
			if (fDebugEn) {debug("  isNumber - " + fLexer.peek());}
			ret = new SVDBLiteralExpr(fLexer.eatTokenR());
		} else if (fLexer.peekKeyword(KW.ONE_STEP)) {
			ret = new SVDBLiteralExpr(fLexer.eatTokenR());
		} else if (fLexer.peekId() || fLexer.peekKeyword(KW.THIS, KW.SUPER)) {
			if (fDebugEn) {debug("  isIdExpression");}
			// expr = hierarchical_identifier(); // idExpr();
			ret = idExpr();
			
			if (fDebugEn) {debug("  postPrimary -- peek: " + fLexer.peek());}
			while (fLexer.peekOperator(OP.COLON2, OP.DOT, OP.LBRACKET)) {
				SVToken t = fLexer.consumeToken();
				// Don't move forward if this is likely to be an assertion sequence
				if (fAssertionExpr.peek()) {
					if (!fLexer.peekOperator()) {
						fLexer.ungetToken(t);
						ret = selector(ret);
					} else {
						fLexer.ungetToken(t);
						break;
					}
				} else {
					fLexer.ungetToken(t);
					ret = selector(ret);
				}
			}
			
		} else {
			error("Expect number, '1step', or identifier ; receive " + fLexer.peek());
		}
		
		
		if (fDebugEn) {debug("<-- delay_value() : " + fLexer.peek());}

		return ret;
	}
	
	public SVDBExpr datatype_or_expression() throws SVParseException {
		if (fLexer.peekKeyword(KW.VIRTUAL, KW.CONST) || fLexer.peekKeyword(SVKeywords.fBuiltinTypesE)) {
			// Know this is a type
			SVDBExpr ret;
			SVDBTypeExpr expr = new SVDBTypeExpr();
			expr.setLocation(fLexer.getStartLocation());
			
			ret = expr;
			
			SVDBTypeInfo info = fParsers.dataTypeParser().data_type(0);
			expr.setTypeInfo(info);
			
			if (fLexer.peekOperator(OP.SQUOTE)) {
				// Cast expression
				
				fLexer.consumeToken();
				ret = new SVDBCastExpr(expr, expression());
			}
			
			return ret;
		} else {
			return expression();
		}
		
	}
	
	public SVDBExpr tf_argument_expression() throws SVParseException {
		if (fLexer.peekKeyword(KW.VIRTUAL)) {
			// Know this is a type
			SVDBTypeExpr expr = new SVDBTypeExpr();
			expr.setLocation(fLexer.getStartLocation());
			
			SVDBTypeInfo info = fParsers.dataTypeParser().data_type(0);
			expr.setTypeInfo(info);
			
			return expr;
		} else if (fLexer.peekOperator(OP.AT)) {
			return clocking_event();
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
			if (fLexer.peekOperator(OP.MUL)) {
				SVDBClockingEventExpr ret = new SVDBClockingEventExpr();
				ret.setLocation(fLexer.getStartLocation());
				ret.setClockingEventType(ClockingEventType.Any);
				return ret;
			} else {
				return expression();
			}
		} finally {
			fEventExpr.pop();
		}
	}
	
	public SVDBExpr variable_lvalue() throws SVParseException {
		SVDBExpr lvalue;
		Context ctxt = fLexer.setContext(Context.Expression);
		
		try {
			if (fDebugEn) {debug("--> variable_lvalue - " + fLexer.peek());}
			if (fLexer.peekOperator(OP.LBRACE)) {
				lvalue = concatenation_or_repetition();
			} else {
				lvalue = unaryExpression();
			}
		} finally {
			fLexer.setContext(ctxt);
		}
		
		if (fDebugEn) {debug("<-- variable_lvalue - " + fLexer.peek());}
		return lvalue;
	}
	
	public SVDBExpr foreach_loopvar() throws SVParseException {
		
		try {
			fForeachLoopvarExpr.push(true);
			return variable_lvalue();
		} finally {
			if (fForeachLoopvarExpr.size() > 0) {
				fForeachLoopvarExpr.pop();
			}
		}
		/*
		SVDBForeachLoopvarExpr loopvar = new SVDBForeachLoopvarExpr();
		
		loopvar.setId(hierarchical_identifier());
	
		fLexer.readOperator(OP.LBRACKET);
		while (true) {
			loopvar.addLoopVar(idExpr());
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.consumeToken();
			} else {
				break;
			}
		}
		fLexer.readOperator(OP.RBRACKET);
	
		return loopvar;
		 */
	}
	
	public SVDBExpr const_or_range_expression() throws SVParseException {
		if (fDebugEn) {debug("--> const_or_range_expression - " + fLexer.peek());}
		SVDBExpr expr = expression();
		if (fLexer.peekOperator(OP.COLON, OP.PLUS_COLON, OP.SUB_COLON)) {
			fLexer.eatToken();
			expr = new SVDBRangeExpr(expr, expression());
		}
		if (fDebugEn) {debug("<-- const_or_range_expression - " + fLexer.peek());}
		return expr;
	}
	
	public SVDBExpr constant_mintypmax_expression() throws SVParseException {
		if (fDebugEn) {debug("<-- constant_mintypmax_expression - " + fLexer.peek());}
		SVDBExpr expr = expression();
		if (fLexer.peekOperator(OP.COLON)) {
			fLexer.eatToken();
			SVDBExpr typ = expression();
			fLexer.readOperator(OP.COLON);
			SVDBExpr max = expression();
			expr = new SVDBMinTypMaxExpr(expr, typ, max);
		}
		
		if (fDebugEn) {debug("<-- constant_mintypmax_expression - " + fLexer.peek());}
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
		
		Context saved_ctxt = fLexer.setContext(Context.Expression);
		
		try {
			if (fDebugEn) {debug("--> expression() " + fLexer.peek());}
			expr = assignmentExpression();

			if (fEventExpr.peek() && fLexer.peekKeyword(KW.IFF)) {
				fLexer.eatToken();
				expr = new SVDBBinaryExpr(expr, "iff", expression());
			}

			if ((fEventExpr.peek() && !fArglistExpr.peek()) 
					&& fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
				expr = new SVDBBinaryExpr(expr, ",", expression());
			}
			if (fDebugEn) {debug("<-- expression() after=" + fLexer.peek());}
		} finally {
			fLexer.setContext(saved_ctxt);
		}
		
		return expr; 
	}
	
	public SVDBExpr hierarchical_identifier() throws SVParseException {
		SVDBExpr ret;
		
		if (fDebugEn) {debug("--> hierarchical_identifier - " + fLexer.peek());}
		String id = fLexer.readIdOrKeyword();

		if (fLexer.peekOperator(OP.LBRACKET)) {
			fLexer.eatToken();
			SVDBArrayAccessExpr aa = new SVDBArrayAccessExpr(
					new SVDBIdentifierExpr(id), expression(), null);
			fLexer.readOperator(OP.RBRACKET);
		
			if (fLexer.peekOperator(OP.DOT, OP.COLON2)) {
				ret = new SVDBFieldAccessExpr(aa, 
						fLexer.peekOperator(OP.COLON2), 
						hierarchical_identifier_int());
			} else {
				ret = aa;
			}
		} else if (fLexer.peekOperator(OP.DOT, OP.COLON2)) {
			ret = new SVDBFieldAccessExpr(
					new SVDBIdentifierExpr(id), 
					fLexer.peekOperator(OP.COLON2), 
					hierarchical_identifier_int());
		} else {
			ret = new SVDBIdentifierExpr(id);
		}
		
		if (fDebugEn) {debug("<-- hierarchical_identifier - " + fLexer.peek());}
		
		return ret;
	}
	
	private SVDBExpr hierarchical_identifier_int() throws SVParseException {
		fLexer.readOperator(OP.DOT, OP.COLON2);

		String id = fLexer.readId();

		if (fLexer.peekOperator(OP.LBRACKET)) {
			fLexer.eatToken();
			SVDBArrayAccessExpr aa = new SVDBArrayAccessExpr(
					new SVDBIdentifierExpr(id), expression(), null);
			fLexer.readOperator(OP.RBRACKET);
		
			if (fLexer.peekOperator(OP.DOT, OP.COLON2)) {
				return new SVDBFieldAccessExpr(aa, 
						fLexer.peekOperator(OP.COLON2), 
						hierarchical_identifier_int());
			} else {
				return aa;
			}
		} else if (fLexer.peekOperator(OP.DOT, OP.COLON2)) {
			return new SVDBFieldAccessExpr(
					new SVDBIdentifierExpr(id), 
					fLexer.peekOperator(OP.COLON2), 
					hierarchical_identifier_int());
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

			if (fLexer.peekKeyword(KW.IFF)) {
				fLexer.eatToken();
				fLexer.readOperator(OP.LPAREN);
				SVDBExpr iff_expr = expression();
				fLexer.readOperator(OP.RPAREN);

				coverpoint.setIFFExpr(iff_expr);
			}
		} catch (EOFException e) {
			e.printStackTrace();
			// Ignore
		}
	}
	
	private static final Set<KW> cp_body_items;
	static {
		cp_body_items = new HashSet<KW>();
		cp_body_items.add(KW.WILDCARD);
		cp_body_items.add(KW.BINS);
		cp_body_items.add(KW.IGNORE_BINS);
		cp_body_items.add(KW.ILLEGAL_BINS);
	}
	
	public void coverpoint_body(SVDBCoverpointExpr coverpoint) throws SVParseException {
		
		try {
			// "wildcard", "bins", "ignore_bins", "illegal_bins", "option", "type_option"
			KW kw_t;
			while (((kw_t = fLexer.peekKeywordE()) != null && cp_body_items.contains(kw_t)) ||
					(fLexer.peek().equals("option") || fLexer.peek().equals("type_option"))) {
				if (fLexer.peek().equals("option") || fLexer.peek().equals("type_option")) {
					String kw = fLexer.eatTokenR();

					fLexer.readOperator(OP.DOT);

					String option = fLexer.readId();

					if (!fLexer.peekString() && !fLexer.peekNumber()) {
						error("unknown option value type \"" + fLexer.peek() + "\"");
					}

					if (kw.equals("option")) {
						coverpoint.addOption(option, fLexer.eatTokenR());
					} else {
						coverpoint.addTypeOption(option, fLexer.eatTokenR());
					}
				} else {
					if (fLexer.peekKeyword(KW.WILDCARD)) {
						fLexer.eatToken();
					}

					KW bins_kw = fLexer.readKeyword(KW.BINS, KW.IGNORE_BINS, KW.ILLEGAL_BINS);
					String bins_id = fLexer.readId();

					SVDBCoverBinsExpr bins = new SVDBCoverBinsExpr(bins_id, bins_kw.getImg());

					if (fLexer.peekOperator(OP.LBRACKET)) {
						fLexer.eatToken();

						bins.setIsArray(true);

						if (!fLexer.peekOperator(OP.RBRACKET)) {
							// read the inner expression
							bins.setArrayExpr(expression());
						}
						fLexer.readOperator(OP.RBRACKET);
					}

					fLexer.readOperator(OP.EQ);

					if (fLexer.peekOperator(OP.LBRACE)) {
						open_range_list(bins.getRangeList());
					} else if (fLexer.peekKeyword(KW.DEFAULT)) {
						fLexer.eatToken();
						bins.setIsDefault(true);
					} else {
						error("Unsupported coverage expression: " + fLexer.peek());
						// 'default' or 'default sequence'
						// ???
					}

					coverpoint.getCoverBins().add(bins);

					if (fLexer.peekOperator(OP.SEMICOLON)) {
						fLexer.eatToken();
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
		SVDBExpr a = implicationExpression();
		
		if (fLexer.peekOperator(SVOperators.fAssignmentOps)) {
			OP op = fLexer.readOperator();
			SVDBExpr rhs = assignmentExpression();
			a = new SVDBAssignExpr(a, op.getImg(), rhs);
		} else if (fLexer.peekKeyword(KW.INSIDE)) {
			a = parseInsideExpr(a);
			
			if (fLexer.peekOperator(SVOperators.fBinaryOps)) {
				a = new SVDBBinaryExpr(a, fLexer.eatTokenR(), expression());
			}
		}

		if (fDebugEn) {debug("<-- assignmentExpression() " + fLexer.peek());}
		return a;
	}
	
	public SVDBExpr implicationExpression() throws SVParseException {
		if (fDebugEn) {debug("--> implicationExpression()"); }
		SVDBExpr a = conditionalExpression();
	
		// Only treat implication as an operator if we're
		// inside a paren expression. This prevents the
		// expression parser from being too greedy and running 
		// into constraint statements
		if (fParenLevel > 0 && fLexer.peekOperator(OP.IMPL, OP.IMPL_BIDIR)) {
			OP op = fLexer.peekOperatorE();
			fLexer.eatToken();
			SVDBExpr rhs = implicationExpression();
			a = new SVDBBinaryExpr(a, op.getImg(), rhs);
		}
		
		if (fDebugEn) {debug("<-- implicationExpression()"); }
		return a;
	}
	
	private SVDBExpr parseInsideExpr(SVDBExpr lhs) throws SVParseException {
		if (fDebugEn) {debug("--> parseInsideExpr() " + fLexer.peek());}
		fLexer.readKeyword(KW.INSIDE);
		SVDBInsideExpr inside = new SVDBInsideExpr(lhs);

		if (fLexer.peekId() &&
				getConfig().allowInsideQWithoutBraces()) {
			inside.getValueRangeList().add(idExpr());
		} else {
			open_range_list(inside.getValueRangeList());
		}

		if (fDebugEn) {debug("<-- parseInsideExpr() " + fLexer.peek());}
		return inside;
	}
	
	public void open_range_list(List<SVDBExpr> list) throws SVParseException {
		if (fDebugEn) {debug("--> open_range_list - " + fLexer.peek());}
		fLexer.readOperator(OP.LBRACE);
		do {
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			}
			if (fLexer.peekOperator(OP.LBRACKET)) {
				list.add(parse_range());
			} else {
				list.add(expression());
			}
		} while (fLexer.peekOperator(OP.COMMA));
		fLexer.readOperator(OP.RBRACE);
		if (fDebugEn) {debug("<-- open_range_list - " + fLexer.peek());}
	}

	public void open_range_list_1(List<SVDBExpr> list) throws SVParseException {
		if (fDebugEn) {debug("--> open_range_list_1 - " + fLexer.peek());}
		do {
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			}
			if (fLexer.peekOperator(OP.LBRACKET)) {
				list.add(parse_range());
			} else {
				list.add(expression());
			}
		} while (fLexer.peekOperator(OP.COMMA));
		if (fDebugEn) {debug("<-- open_range_list_1 - " + fLexer.peek());}
	}
	
	public SVDBRangeExpr parse_range() throws SVParseException {
		if (fDebugEn) {debug("--> parse_range - " + fLexer.peek());}
		fLexer.readOperator(OP.LBRACKET);
		SVDBExpr left = expression();
		SVDBExpr right;
		fLexer.readOperator(OP.COLON, OP.SUB_COLON, OP.PLUS_COLON);
		if (fLexer.peekOperator(OP.DOLLAR)) {
			fLexer.eatToken();
			right = new SVDBRangeDollarBoundExpr();
		} else {
			right = expression();
		}
		fLexer.readOperator(OP.RBRACKET);
		
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
		
		if (fLexer.peekOperator(OP.TERNARY)) {
			fLexer.eatToken();
			SVDBExpr lhs = a;
			// We are going to have a : here, make sure we don't mistake the : for a label identifier
			fEnableNameMappedPrimary.push(false);
			SVDBExpr mhs = expression();
			fEnableNameMappedPrimary.pop();
			fLexer.readOperator(OP.COLON);

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
		
		while (fLexer.peekOperator(OP.OR2) || 
				(fEventExpr.peek() && fLexer.peekKeyword(KW.OR))) {
			String op = fLexer.eatTokenR();
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
		boolean is_and2;
		
		while ((is_and2=fLexer.peekOperator(OP.AND2)) ||
				(fEventExpr.peek() && fLexer.peekKeyword(KW.AND))) {
			fLexer.eatToken();
			a = new SVDBBinaryExpr(a, 
					(is_and2)?"&&":"AND", inclusiveOrExpression());
		}
		if (fDebugEn) {debug("<-- conditionalAndExpression()");}
		return a;
	}
	
	public SVDBExpr inclusiveOrExpression() throws SVParseException {
		if (fDebugEn) {debug("--> inclusiveOrExpression");}
		SVDBExpr a = exclusiveOrExpression();
		
		while (fLexer.peekOperator(OP.OR)) {
			fLexer.eatToken();
			a = new SVDBBinaryExpr(a, "|", exclusiveOrExpression());
		}
		
		if (fDebugEn) {debug("<-- inclusiveOrExpression");}
		return a;
	}
	
	public SVDBExpr exclusiveOrExpression() throws SVParseException {
		if (fDebugEn) {debug("--> exclusiveOrExpression");}
		SVDBExpr a = exclusiveNorExpression1();
		
		while (fLexer.peekOperator(OP.XOR)) {
			fLexer.eatToken();
			a = new SVDBBinaryExpr(a, "^", exclusiveNorExpression1());
		}
		
		if (fDebugEn) {debug("<-- exclusiveOrExpression");}
		return a;
	}
	
	public SVDBExpr exclusiveNorExpression1() throws SVParseException {
		if (fDebugEn) {debug("--> exclusiveNorExpression1");}
		SVDBExpr a = exclusiveNorExpression2();
		
		while (fLexer.peekOperator(OP.XOR_NEG)) {
			fLexer.eatToken();
			a = new SVDBBinaryExpr(a, "^~", exclusiveNorExpression2());
		}
		
		if (fDebugEn) {debug("<-- exclusiveNorExpression1");}
		return a;
	}
	
	public SVDBExpr exclusiveNorExpression2() throws SVParseException {
		if (fDebugEn) {debug("--> exclusiveNorExpression2");}
		SVDBExpr a = andExpression();
		
		while (fLexer.peekOperator(OP.NEG_XOR)) {
			fLexer.eatToken();
			a = new SVDBBinaryExpr(a, "~^", andExpression());
		}
		
		if (fDebugEn) {debug("<-- exclusiveNorExpression2");}
		return a;
	}
	
	public SVDBExpr andExpression() throws SVParseException {
		if (fDebugEn) {debug("--> andExpression");}
		SVDBExpr a = equalityExpression();
		
		while (fLexer.peekOperator(OP.AND)) {
			fLexer.eatToken();
			a = new SVDBBinaryExpr(a, "&", equalityExpression());
		}
		
		if (fDebugEn) {debug("<-- andExpression");}
		return a;
	}
	
	public SVDBExpr equalityExpression() throws SVParseException {
		if (fDebugEn) {debug("--> equalityExpression");}
		SVDBExpr a = relationalExpression();
		
		while (fLexer.peekOperator(OP.EQ2, OP.NOT_EQ, OP.EQ3, OP.NOT_EQ2, OP.EQ2_TERN, OP.NOT_EQ_TERN)) {
			a = new SVDBBinaryExpr(a, fLexer.readOperator().getImg(), relationalExpression());
		}
		
		if (fDebugEn) {debug("<-- equalityExpression");}
		return a;
	}
	
	public SVDBExpr relationalExpression() throws SVParseException {
		if (fDebugEn) {debug("--> relationalExpression");}
		SVDBExpr a = shiftExpression();
		
		while (fLexer.peekOperator(OP.LT, OP.GT, OP.LE, OP.GE)) {
			a = new SVDBBinaryExpr(a, fLexer.readOperator().getImg(), shiftExpression());
		}
		
		if (fDebugEn) {debug("<-- relationalExpression");}
		return a;
	}
	
	public SVDBExpr shiftExpression() throws SVParseException {
		if (fDebugEn) {debug("--> shiftExpression");}
		SVDBExpr a = additiveExpression();
		
		while (fLexer.peekOperator(OP.LSHIFT, OP.LSHIFT3, OP.RSHIFT, OP.RSHIFT3)) {
			a = new SVDBBinaryExpr(a, fLexer.readOperator().getImg(), additiveExpression());
		}
		
		if (fDebugEn) {debug("<-- shiftExpression");}
		return a;
	}
	
	public SVDBExpr additiveExpression() throws SVParseException {
		if (fDebugEn) {debug("--> additiveExpression");}
		SVDBExpr a = multiplicativeExpression();
		
		while (fLexer.peekOperator(OP.PLUS, OP.MINUS)) {
			a = new SVDBBinaryExpr(a, fLexer.readOperator().getImg(), multiplicativeExpression());
		}
		if (fDebugEn) {debug("<-- additiveExpression");}
		return a;
	}
	
	public SVDBExpr multiplicativeExpression() throws SVParseException {
		if (fDebugEn) {debug("--> multiplicativeExpression " + fLexer.peek());}
		SVDBExpr a = unaryExpression();
		
		while (fLexer.peekOperator(OP.MUL, OP.DIV, OP.MOD, OP.MUL2)) {
			a = new SVDBBinaryExpr(a, fLexer.readOperator().getImg(), unaryExpression());
		}
		if (fDebugEn) {debug("<-- multiplicativeExpression");}
		return a;
	}
	
	private static final Set<OP>	op_set;
	static {
		op_set = new HashSet<ISVOperators.OP>();
		op_set.add(OP.PLUS);
		op_set.add(OP.MINUS);
		op_set.add(OP.NEG);
		op_set.add(OP.NOT);
		op_set.add(OP.AND);
		op_set.add(OP.NEG_AND);
		op_set.add(OP.OR);
		op_set.add(OP.NEG_OR);
		op_set.add(OP.XOR);
		op_set.add(OP.NEG_XOR);
		op_set.add(OP.XOR_NEG);
	}
	
	public SVDBExpr unaryExpression() throws SVParseException {
		if (fDebugEn) {debug("--> unaryExpression " + fLexer.peek());}
		if (fLexer.peekOperator(OP.INC, OP.DEC)) {
			return new SVDBIncDecExpr(fLexer.readOperator().getImg(), unaryExpression());
		} else if (fEventExpr.peek() && fLexer.peekKeyword(KW.POSEDGE, KW.NEGEDGE, KW.EDGE)) {
			SVDBExpr ret = new SVDBUnaryExpr(fLexer.eatTokenR(), expression());
			if (fLexer.peekKeyword(KW.IFF)) {
				fLexer.eatToken();
				ret = new SVDBBinaryExpr(ret, "iff", expression());
			}
			return ret;
		}
		if (op_set.contains(fLexer.peekOperatorE()) ||
				(fAssertionExpr.peek() && 
						(fLexer.peekOperator(OP.MUL) || fLexer.peekKeyword(KW.NOT)))) {
			String op = fLexer.eatTokenR();
			SVDBUnaryExpr ret = new SVDBUnaryExpr(op, unaryExpression());
			
			if (fDebugEn) {debug("<-- unaryExpression " + op);}
			return ret; 
		} else if (fLexer.peekOperator(OP.SQUOTE)) {
			return assignment_pattern_expr();
		}

		SVDBExpr a = primary();
		
		if (fDebugEn) {debug("unaryExpr -- peek: " + fLexer.peek());}
		while (fLexer.peekOperator(OP.COLON2, OP.DOT, OP.LBRACKET)) {
			SVToken t = fLexer.consumeToken();
			if (fLexer.peekOperator(OP.MUL)) {
				// This is a coverpoint transition expression
				fLexer.ungetToken(t);
				break;
			} else if (fAssertionExpr.peek()) {
				// Don't move forward if this is likely to be an assertion sequence
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

		if (fLexer.peekOperator(OP.SQUOTE)) {
			SVToken tok = fLexer.consumeToken();
			if (fLexer.peekOperator(OP.LBRACE)) {
				fLexer.ungetToken(tok);
				a = assignment_pattern_expr();
			} else {
//				fLexer.ungetToken(tok);
				if (fDebugEn) {debug("    castExpr " + fLexer.peek());}
//				fLexer.eatToken();
				// MSB: new cast expression
				a = new SVDBCastExpr(a, expression());
			}
		}

		while (fLexer.peekOperator(OP.INC, OP.DEC)) {
			a = new SVDBIncDecExpr(fLexer.readOperator().getImg(), a);
		}
		
		if (fLexer.peekKeyword(KW.INSIDE)) {
			a = parseInsideExpr(a);
		}
		
		return a;
	}
	
	private SVDBExpr assignment_pattern_expr() throws SVParseException {
		SVDBExpr ret_top;
		fLexer.readOperator(OP.SQUOTE);
		fLexer.readOperator(OP.LBRACE);
		if (fDebugEn) {debug("    assignmentPattern");}
		
		if (fLexer.peekOperator(OP.RBRACE)) {
			// empty_queue: '{}
			fLexer.eatToken();
			ret_top = new SVDBConcatenationExpr();
		} else {

			try {
				fEnableNameMappedPrimary.push(true);
				// This could be an associative-array initialization statement
				SVDBExpr expr1 = expression();
				if (fLexer.peekOperator(OP.LBRACE)) {
					// repetition
					SVDBAssignmentPatternRepeatExpr ret = new SVDBAssignmentPatternRepeatExpr(expr1);

					fLexer.eatToken(); // {
					while (true) {
						SVDBExpr expr = expression();

						ret.getPatternList().add(expr);

						if (fLexer.peekOperator(OP.COMMA)) {
							fLexer.eatToken();
						} else {
							break;
						}
					}
					fLexer.readOperator(OP.RBRACE);
					ret_top = ret;
				} else {
					SVDBAssignmentPatternExpr ret = new SVDBAssignmentPatternExpr();
					ret.getPatternList().add(expr1);

					while (fLexer.peekOperator(OP.COMMA)) {
						fLexer.eatToken();
						SVDBExpr expr = expression();

						ret.getPatternList().add(expr);
					}
					ret_top = ret;
				}
				fLexer.readOperator(OP.RBRACE);
			} finally {
				fEnableNameMappedPrimary.pop();
			}
		}
		return ret_top;
	}
	
	public SVDBExpr primary() throws SVParseException {
		if (fDebugEn) {debug("--> primary() - " + fLexer.peek());}
		SVDBExpr ret = null;
		
		if (fLexer.peekOperator(OP.LPAREN)) {
			if (fDebugEn) {debug("  Found paren in primary");}
			fLexer.eatToken();
			
			// if (isType) {
			// TODO
			//

			SVDBExpr a = null;
			try {
				fParenLevel++;
				a = expression();
			} finally {
				fParenLevel--;
			}
			
			// TODO: save expression
			if (fLexer.peekOperator(OP.COLON)) {
				fLexer.eatToken();
				SVDBExpr expr = fParsers.exprParser().expression();
				if (fLexer.peekOperator(OP.COLON)) {
					fLexer.eatToken();
					expr = fParsers.exprParser().expression();
				}
			} else if (fLexer.peekKeyword(KW.DIST) && getConfig().allowDistInsideParens()) {
				// TODO: 
				SVDBConstraintDistListStmt dist_stmt = new SVDBConstraintDistListStmt();
				fLexer.eatToken();
				fParsers.constraintParser().dist_list(dist_stmt);				
			}
			
			fLexer.readOperator(OP.RPAREN);
			
			// cast
			// '(' expression() ')' unaryExpression
			if (fLexer.peekNumber() || fLexer.peekId() ||
					fLexer.peekOperator(OP.LPAREN, OP.NEG, OP.NOT) || 
					fLexer.peekKeyword(KW.THIS, KW.SUPER, KW.NEW)) {
				fLexer.eatToken(); // '
				SVDBExpr rhs = unaryExpression();
				if (fSaveExpr) {
					ret = new SVDBCastExpr(a, rhs);
				}
			} else if (fSaveExpr) {
				ret = new SVDBParenExpr(a);
			}
		} else {
			// TODO: must finish and figure out what's going on
			if (fLexer.peekNumber()) {
				if (fDebugEn) {debug("-- primary is a number");}
				SVToken tmp = (fSaveExpr)?fLexer.consumeToken():null;
				if (fEnableNameMappedPrimary.peek() && fLexer.peekOperator(OP.COLON)) {
					fLexer.eatToken();
					SVDBExpr rhs = expression();
					if (fSaveExpr) {
						ret = new SVDBNameMappedExpr(tmp.getImage(), rhs);
					}
				} else if (fSaveExpr) {
					ret = new SVDBLiteralExpr(tmp.getImage());
				}
			} else if (fLexer.peekOperator(OP.DOLLAR)) {
				fLexer.eatToken();
				if (fSaveExpr) {
					ret = new SVDBRangeDollarBoundExpr();
				}
			} else if (fLexer.peekString()) {
				if (fDebugEn) {debug("-- primary is a string");}
				SVToken tmp = (fSaveExpr)?fLexer.consumeToken():null;
				if (fEnableNameMappedPrimary.peek() && fLexer.peekOperator(OP.COLON)) {
					if (fDebugEn) {debug("-- primary is a name-mapped string");}
					fLexer.eatToken();
					ret = new SVDBNameMappedExpr(tmp.getImage(), expression());
				} else {
					if (fDebugEn) {debug("-- primary is a ordinary string");}
					ret = new SVDBStringExpr(tmp.getImage());
				}
			} else if (fLexer.peekKeyword(KW.NULL)) {
				if (fDebugEn) {debug("-- primary is 'null'");}
				fLexer.eatToken();
				ret = new SVDBNullExpr();
			} else if (fLexer.isIdentifier() || 
					SVKeywords.isBuiltInType(fLexer.peek()) ||
					fLexer.peekKeyword(KW.NEW, KW.DEFAULT, KW.LOCAL, KW.CONST) ||
					// TODO: optimize
					fLexer.peekKeyword(SVKeywords.fAMSFilterFuncs)) {
				if (fDebugEn) {
					debug("  primary \"" + fLexer.getImage() + "\" is identifier or built-in type");
				}
				SVToken id_tok = fLexer.consumeToken();
				String id = id_tok.getImage();
				
				if (fLexer.peekOperator(OP.LPAREN_MUL)) {
					fParsers.attrParser().parse(null);
				}
				
				if (fLexer.peekOperator(OP.HASH)) {
					if (fDebugEn) {
						debug("Parameterized identifier");
					}
					// Parameterized identifier
					ret = new SVDBParamIdExpr(id);
					/*
					fLexer.eatToken(); // #
					fLexer.readOperator(OP.LPAREN);
					 */
					// Catch case where no parameters are specified in the parameter list
					boolean name_mapped = false;
					SVDBParamValueAssignList plist = parsers().paramValueAssignParser().parse(true);
					

					/**
					while (fLexer.peek() != null && !fLexer.peekOperator(OP.RPAREN)) {
						// TODO: should preserve the 
						((SVDBParamIdExpr)ret).addParamExpr(datatype_or_expression());
						if (fLexer.peekOperator(OP.COMMA)) {
							fLexer.eatToken();
						} else {
							break;
						}
					}
					fLexer.readOperator(OP.RPAREN);
					 */
				} else if (fLexer.peekOperator(OP.LPAREN) || fLexer.peekKeyword(KW.WITH)) {
					if (id.equals("randomize")) {
						ret = randomize_call(null);
					} else if (fLexer.peekOperator(OP.LPAREN)) {
						ret = tf_args_call(null, id_tok);
					} else {
						ret = tf_noargs_with_call(null, id);
					}
				} else if (id.equals("new")) {
					ret = ctor_call();
				} else if (fLexer.peekKeyword(SVKeywords.fBuiltinDeclTypesE) ||
						fLexer.peekKeyword(KW.CONST)) {
					SVStringTokenListener l = new SVStringTokenListener();
					fLexer.addTokenListener(l);
					try {
						fLexer.eatToken();
						if (fLexer.peekKeyword(KW.SIGNED, KW.UNSIGNED)) {
							fLexer.eatToken();
						}
					} finally {
						fLexer.removeTokenListener(l);
					}
					ret = new SVDBIdentifierExpr(l.toString());
				} else {
					// ID or 'default'
					if (fEnableNameMappedPrimary.peek() && fLexer.peekOperator(OP.COLON)) {
						fLexer.eatToken();
						if (fDebugEn) {debug("    nameMappedExpr");}
						ret = new SVDBNameMappedExpr(id, expression());
					} else {
						ret = new SVDBIdentifierExpr(id);
					}
					if (fDebugEn) {debug("  after id-read: " + fLexer.peek());}
				}
			} else if (fLexer.peekOperator(OP.LBRACE)) {
				// concatenation
				ret = concatenation_or_repetition();
				
				if (fEnableNameMappedPrimary.peek() && fLexer.peekOperator(OP.COLON)) {
					fLexer.eatToken();
					SVDBExpr rhs = expression();
					if (fSaveExpr) {
						ret = new SVDBNameMappedExpr(ret, rhs);
					}
				} 
			} else if (fLexer.peekKeyword(KW.THIS)) {
				fLexer.eatToken();
				ret = new SVDBIdentifierExpr("this");
			} else if (fLexer.peekKeyword(KW.SUPER)) {
				fLexer.eatToken();
				ret = new SVDBIdentifierExpr("super");
			} else if (fLexer.peekKeyword(KW.VOID)) {
				fLexer.eatToken();
				ret = new SVDBIdentifierExpr("void");
			} else if (fEventExpr.peek() && fLexer.peekOperator(OP.AT)) {
				ret = clocking_event();
			} else if (fEventExpr.peek() && fLexer.peekOperator(OP.HASH2)) {
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
		fLexer.readOperator(OP.LBRACE);
		if (fLexer.peekOperator(OP.RBRACE)) {
			// empty_queue
			fLexer.eatToken();
			expr = new SVDBConcatenationExpr();
		} else if (fLexer.peekOperator(OP.LSHIFT, OP.RSHIFT)) {
			if (fDebugEn) {debug("streaming operator");}
			// TODO: preserve this portion of expression
			fLexer.eatToken();
			
			if (fLexer.peekKeyword(SVKeywords.fBuiltinTypesE)) {
				expr = new SVDBTypeExpr(fParsers.dataTypeParser().data_type(0));
			} else if (!fLexer.peekOperator(OP.LBRACE)) {
				expr = new SVDBLiteralExpr(fLexer.eatTokenR());
			}
			
			if (fDebugEn) {debug("post-datatype: " + fLexer.peek());}
			
			fLexer.readOperator(OP.LBRACE);
			while (fLexer.peek() != null) {
				expression();
				
				if (fDebugEn) {debug("pre-with: " + fLexer.peek());}
				if (fLexer.peekKeyword(KW.WITH)) {
					fLexer.eatToken();
					fLexer.readOperator(OP.LBRACKET);
					expression();
					if (fLexer.peekOperator(OP.COLON, OP.PLUS_COLON, OP.SUB_COLON)) {
						fLexer.eatToken();
						expression();
					}
					fLexer.readOperator(OP.RBRACKET);
				}
				
				if (fLexer.peekOperator(OP.COMMA)) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
			fLexer.readOperator(OP.RBRACE);
			fLexer.readOperator(OP.RBRACE);
				
			expr = new SVDBConcatenationExpr();
		} else {
			try {
//				fEnableNameMappedPrimary = true;
				SVDBExpr expr0 = expression();

				// concatenation or repetition
				if (fLexer.peekOperator(OP.LBRACE)) {
					if (fDebugEn) {debug("repetition");}
					fLexer.eatToken();
					// repetition
					SVDBAssignmentPatternRepeatExpr ret = new SVDBAssignmentPatternRepeatExpr(expr);
					ret.setRepeatExpr(expr0);

					while (fLexer.peek() != null) {
						ret.getPatternList().add(expression());
						if (fLexer.peekOperator(OP.COMMA)) {
							fLexer.eatToken();
						} else {
							break;
						}
					}
					fLexer.readOperator(OP.RBRACE); // end of inner expression
					fLexer.readOperator(OP.RBRACE);
					expr = ret;
				} else {
					
					if (fLexer.peekOperator(OP.COMMA)) {
						if (fDebugEn) {debug("concatenation");}
						SVDBConcatenationExpr ret = new SVDBConcatenationExpr();
						ret.getElements().add(expr0);

						while (fLexer.peekOperator(OP.COMMA)) {
							fLexer.eatToken();
							ret.getElements().add(expression());
						}
						
						expr = ret;
					} else if (fLexer.peekOperator(OP.COLON)) {
						SVDBAssociativeArrayAssignExpr ret = new SVDBAssociativeArrayAssignExpr();
						
						// Initial
						SVDBAssociativeArrayElemAssignExpr elem = new SVDBAssociativeArrayElemAssignExpr();
						elem.setKey(expr0);
						fLexer.eatToken();
						elem.setValue(expression());
						ret.addElement(elem);
						
						while (fLexer.peekOperator(OP.COMMA)) {
							fLexer.eatToken();
							
							elem = new SVDBAssociativeArrayElemAssignExpr();
							elem.setKey(expression());
							fLexer.readOperator(OP.COLON);
							elem.setValue(expression());
							ret.addElement(elem);
						}
						
					}

					fLexer.readOperator(OP.RBRACE);

				}
			} finally {
//				fEnableNameMappedPrimary = false;
			}
		}
		if (fDebugEn) {debug("<-- concatenation_or_repetition()");}
		return expr;
	}
	
	public List<SVDBExpr> arguments() throws SVParseException {
		List<SVDBExpr> arguments = null;
		
		if (fDebugEn) {debug("--> arguments()");}
		fLexer.readOperator(OP.LPAREN);
	
		// An argument list (tf-call) is neither an assertion nor an event context
		fAssertionExpr.push(false);
		fArglistExpr.push(true);
	
		try {
			if (fLexer.peekOperator(OP.RPAREN)) {
				fLexer.eatToken();
				return new ArrayList<SVDBExpr>();
			}
		
			arguments = argumentList();
		
			fLexer.readOperator(OP.RPAREN);
		} finally {
			fAssertionExpr.pop();
			fArglistExpr.pop();
		}
		if (fDebugEn) {debug("<-- arguments()");}
		return arguments;
	}
	
	private List<SVDBExpr> argumentList() throws SVParseException {
		List<SVDBExpr> arguments = new ArrayList<SVDBExpr>();
		if (fDebugEn) {debug("--> argumentList() " + fLexer.peek());}
		
		for (;;) {
			if (fDebugEn) {debug("   argument: " + fLexer.peek());}
			if (fLexer.peekOperator(OP.DOT)) {
				// named argument
				fLexer.eatToken();
				SVDBNamedArgExpr arg_expr = new SVDBNamedArgExpr();
				String name = fLexer.readId();
				arg_expr.setArgName(name);
				fLexer.readOperator(OP.LPAREN);
				if (fLexer.peekOperator(OP.RPAREN)) {
					// empty argument specifier
					arg_expr.setExpr(new SVDBLiteralExpr(""));
				} else {
					arg_expr.setExpr(tf_argument_expression());
				}
				fLexer.readOperator(OP.RPAREN);
				arguments.add(arg_expr);
			} else if (fLexer.peekOperator(OP.COMMA, OP.RPAREN)) {
				// default value for this parameter
				arguments.add(new SVDBLiteralExpr(""));
			} else {
				if (fDebugEn) {debug("   --> argument_expr " + fLexer.peek());}
				arguments.add(tf_argument_expression());
				if (fDebugEn) {debug("   <-- argument_expr " + fLexer.peek());}
			}
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		
		if (fDebugEn) {debug("<-- argumentList()");}
		return arguments;
	}
	
	public SVDBExpr selector(SVDBExpr expr) throws SVParseException {
		if (fDebugEn) {debug("--> selector() " + fLexer.peek());}
		if (fLexer.peekOperator(OP.DOT, OP.COLON2)) {
			String q = fLexer.eatTokenR();
			
			fLexer.peek();
			if (fLexer.isIdentifier() || fLexer.peekKeyword(SVKeywords.fBuiltinSelectorMethods)) {
				SVToken id_tok = fLexer.consumeToken();
				String id = id_tok.getImage();
				
				if (fLexer.peekOperator(OP.LPAREN_MUL)) {
					fParsers.attrParser().parse(null);
				}

				if (fLexer.peekOperator(OP.LPAREN) || fLexer.peekKeyword(KW.WITH)) {
					if (id.equals("randomize")) {
						return randomize_call(expr);
					} else if (fLexer.peekOperator(OP.LPAREN)){
						return tf_args_call(expr, id_tok);
					} else {
						return tf_noargs_with_call(expr, id);
					}
				}
				if (q.equals(".")) {
					// '.' identifier
					if (fDebugEn) {debug("<-- selector() - IdentifierExpr");}
					return new SVDBFieldAccessExpr(expr, (q.equals("::")), 
							new SVDBIdentifierExpr(id));
				} else {
					// '::' identifier|parameterized_classtype
					
					if (fLexer.peekOperator(OP.HASH)) {
						// Parameterized class type
						fLexer.ungetToken(id_tok);
						SVDBTypeExpr rhs = new SVDBTypeExpr();
						rhs.setLocation(fLexer.getStartLocation());
					
						SVDBTypeInfo info = fParsers.dataTypeParser().data_type(0);
						rhs.setTypeInfo(info);
						
						if (fDebugEn) {
							debug("  rhs=" + rhs);
							debug("<-- selector() - DataType (" + fLexer.peek() + ")");
						}
						expr = new SVDBFieldAccessExpr(expr, true, rhs);
						
						if (fLexer.peekOperator(OP.COLON2)) {
							return selector(expr);
						} else {
							return expr;
						}
					} else {
						fLexer.ungetToken(id_tok);
						SVDBExpr id_expr = primary();
					
						// Sometimes the id parse fails -- especially while working with incomplete data
						if (id_expr == null) {
							id_expr = new SVDBIdentifierExpr(id);
						}
						if (fDebugEn) {debug("<-- selector() - IdentifierExpr(2)");}
						return new SVDBFieldAccessExpr(expr, (q.equals("::")), id_expr);
					}
				}
			}
		}

		// TODO: keyword new
		// TODO: keyword class`
		
		if (fLexer.peekOperator(OP.LBRACKET)) {
			SVDBExpr ret = null;
			if (fDebugEn) {debug("primary() -- operator " + fLexer.peek());}
			// '[' expression ']'
			fLexer.eatToken();
			
			SVDBExpr low = expression();
			SVDBExpr high = null;

			// TODO: should probably preserve array-bounds method
			if (fLexer.peekOperator(OP.COLON, OP.PLUS_COLON, OP.SUB_COLON)) {
				fLexer.eatToken();
				high = expression();
				ret = new SVDBArrayAccessExpr(expr, low, high);
			} else if (fForeachLoopvarExpr.peek() && fLexer.peekOperator(OP.COMMA)) {
				// multi-variable foreach index expression
				SVDBForeachLoopvarExpr loopvar = new SVDBForeachLoopvarExpr();
				loopvar.setId(expr);
			
				loopvar.addLoopVar(low);
				do {
					fLexer.consumeToken();
					loopvar.addLoopVar(idExpr());
				} while (fLexer.peekOperator(OP.COMMA));

				ret = loopvar;
			} else {
				ret = new SVDBArrayAccessExpr(expr, low, high);
			}
			
			fLexer.readOperator(OP.RBRACKET);
			if (expr == null) {
				error("array expr == null");
			}
			if (fDebugEn) {debug("<-- selector()");}
			return ret; 
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
			if (fLexer.peekOperator(OP.LPAREN)) {
				arguments = arguments();
			}

			rand_call = new SVDBRandomizeCallExpr(target, "randomize", arguments);

			if (fLexer.peekKeyword(KW.WITH)) {
				fLexer.eatToken();
				// constraint block
				Context saved_ctxt = fLexer.setContext(SVLexer.Context.Default);
				rand_call.setWithBlock(fParsers.constraintParser().constraint_set(true, false, true));
				fLexer.setContext(saved_ctxt);
			}
		} finally {
			fAssertionExpr.pop();
			fEventExpr.pop();
		}
		return rand_call;
	}
	
	private SVDBTFCallExpr tf_args_call(SVDBExpr target, SVToken id) throws SVParseException {
		SVDBTFCallExpr tf = new SVDBTFCallExpr(target, id.getImage(), arguments());	
		tf.setLocation(id.getStartLocation());
		
		if (fLexer.peekKeyword(KW.WITH)) {
			fLexer.eatToken();
			fLexer.readOperator(OP.LPAREN);
			tf.setWithExpr(expression());
			fLexer.readOperator(OP.RPAREN);
		}
		
		return tf;
	}
	
	private SVDBTFCallExpr tf_noargs_with_call(SVDBExpr target, String id) throws SVParseException {
		SVDBTFCallExpr tf = new SVDBTFCallExpr(target, id, null);
		
		// TODO:
		if (fLexer.peekKeyword(KW.WITH)) {
			fLexer.eatToken();
			if (fLexer.peekOperator(OP.LBRACKET)) {
				fLexer.eatToken();
				tf.setWithExpr(expression());
				if (fLexer.peekOperator(OP.COLON, OP.PLUS_COLON, OP.SUB_COLON)) {
					fLexer.eatToken();
					expression();
				}
				fLexer.readOperator(OP.RBRACKET);
			} else {
				fLexer.readOperator(OP.LPAREN);
				tf.setWithExpr(expression());
				fLexer.readOperator(OP.RPAREN);
			}
		}
		
		return tf; 
	}
	
	private SVDBCtorExpr ctor_call() throws SVParseException {
		if (fDebugEn) {
			debug("--> ctor_call()");
		}
		SVDBCtorExpr ctor = new SVDBCtorExpr();
		if (fLexer.peekOperator(OP.LBRACKET)) {
			// array constructor
			fLexer.eatToken();
			ctor.setCtorType(CtorType.CtorType_Dim);
			ctor.setArg(expression());
			fLexer.readOperator(OP.RBRACKET);
		}
		if (fLexer.peekOperator(OP.LPAREN)) {
			ctor.setCtorType(CtorType.CtorType_Args);
			ctor.setArgs(arguments());
		} else if (fLexer.peekKeyword() || fLexer.peekId()) {
			ctor.setCtorType(CtorType.CtorType_Expr);
			ctor.setArg(expression());
		}
		
		if (fDebugEn) {
			debug("--> ctor_call()");
		}
		return ctor;
	}

	public SVDBIdentifierExpr idExpr() throws SVParseException {
		long start = fLexer.getStartLocation();
		SVDBIdentifierExpr ret = null;
		if (fLexer.peekKeyword(KW.THIS, KW.SUPER)) {
			ret = new SVDBIdentifierExpr(fLexer.eatTokenR());
		} else {
			ret = new SVDBIdentifierExpr(fLexer.readId());
		}
		ret.setLocation(start);
		
		return ret;
	}
	
	public SVDBLiteralExpr literalExpr() throws SVParseException {
		long start = fLexer.getStartLocation();
		SVDBLiteralExpr ret = new SVDBLiteralExpr(fLexer.readNumber());
		ret.setLocation(start);
		
		return ret;
	}
}
