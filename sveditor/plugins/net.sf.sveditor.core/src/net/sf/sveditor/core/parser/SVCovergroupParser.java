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
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBCovergroup;
import net.sf.sveditor.core.db.SVDBCovergroup.BinsKW;
import net.sf.sveditor.core.db.SVDBCoverpoint;
import net.sf.sveditor.core.db.SVDBCoverpointBins;
import net.sf.sveditor.core.db.SVDBCoverpointBins.BinsType;
import net.sf.sveditor.core.db.SVDBCoverpointCross;
import net.sf.sveditor.core.db.expr.SVDBBinaryExpr;
import net.sf.sveditor.core.db.expr.SVDBCrossBinsSelectConditionExpr;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBFieldAccessExpr;
import net.sf.sveditor.core.db.expr.SVDBIdentifierExpr;
import net.sf.sveditor.core.db.expr.SVDBParenExpr;
import net.sf.sveditor.core.db.expr.SVDBUnaryExpr;
import net.sf.sveditor.core.db.stmt.SVDBCoverageCrossBinsSelectStmt;
import net.sf.sveditor.core.db.stmt.SVDBCoverageOptionStmt;

public class SVCovergroupParser extends SVParserBase {
	
	public SVCovergroupParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(ISVDBAddChildItem parent) throws SVParseException {
		long start = fLexer.getStartLocation();
		fLexer.readKeyword(KW.COVERGROUP);
		String cg_name = fLexer.readId();

		SVDBCovergroup cg = new SVDBCovergroup(cg_name);
		cg.setLocation(start);

		while (fLexer.peekOperator(OP.LPAREN)) {
			cg.setParamPort(parsers().tfPortListParser().parse());
		}

		if (fLexer.peekOperator(OP.AT2)) {
			// block_event_expression
			error("block_event_expression not supported for covergroup sampling");
		} else if (fLexer.peekOperator(OP.AT)) {
			cg.setCoverageEvent(parsers().exprParser().clocking_event());
		} else if (fLexer.peekKeyword(KW.WITH)) {
			// with function sample not completely supported 
			// TODO : just run to the end of the covergroup, swallowing the lot
			while (fLexer.peek() != null && !fLexer.peekOperator(OP.SEMICOLON))  {
				fLexer.eatToken();
			}
		}
		
		fLexer.readOperator(OP.SEMICOLON);
		parent.addChildItem(cg);

		enter_type_scope(cg);
		try {
			// Skip statements
			while (fLexer.peek() != null && !fLexer.peekKeyword(KW.ENDGROUP)) {
				ISVDBChildItem cov_item;

				if (isOption()) {
					cov_item = coverage_option();
				} else {
					cov_item = coverage_spec();
				}
				cg.addItem(cov_item);
			}

			cg.setEndLocation(fLexer.getStartLocation());
			fLexer.readKeyword(KW.ENDGROUP);
			
			if (fLexer.peekOperator(OP.COLON)) {
				fLexer.eatToken();
				fLexer.readId(); // labeled group
			}
		} catch (SVParseException e) {
			// attempt to recover from the error
			while (fLexer.peek() != null && 
					!fLexer.peekKeyword(KW.ENDGROUP, KW.CLASS, KW.MODULE, KW.FUNCTION,
							KW.TASK, KW.ENDCLASS, KW.ENDMODULE)) {
				fLexer.eatToken();
			}
			cg.setEndLocation(fLexer.getStartLocation());
			if (fLexer.peekKeyword(KW.ENDGROUP)) {
				fLexer.eatToken();
				if (fLexer.peekOperator(OP.COLON)) {
					fLexer.eatToken();
					fLexer.readId(); // labeled group
				}
			}
		} finally {
			leave_type_scope(cg);
		}
		
	}
	
	private SVDBCoverageOptionStmt coverage_option() throws SVParseException {
		// option or type_option
		long start = fLexer.getStartLocation();
		String type = fLexer.eatTokenR();
		fLexer.readOperator(OP.DOT);
		String name = fLexer.readId();
		
		SVDBCoverageOptionStmt opt = new SVDBCoverageOptionStmt(name, type.equals("type_option"));
		opt.setLocation(start);
		fLexer.readOperator(OP.EQ);
		opt.setExpr(parsers().exprParser().expression());
		
		fLexer.readOperator(OP.SEMICOLON);
		
		return opt;
	}
	
	private ISVDBChildItem coverage_spec() throws SVParseException {
		ISVDBChildItem ret = null;
		String name = null;
		long start = fLexer.getStartLocation();
		if (fLexer.peekId()) {
			name = fLexer.readId();
			fLexer.readOperator(OP.COLON);
		}
		
		KW type = fLexer.readKeyword(KW.COVERPOINT, KW.CROSS);
		if (type == KW.COVERPOINT) {
			if (name == null)  {
				name = "coverpoint";
			}
			SVDBCoverpoint cp = new SVDBCoverpoint(name);
			cp.setLocation(start);
			cover_point(cp);
			ret = cp;
		} else {
			if (name == null)  {
				name = "cross";
			}
			SVDBCoverpointCross cp = new SVDBCoverpointCross(name);
			cp.setLocation(start);
			cover_cross(cp);
			ret = cp;
		}
		
		return ret;
	}
	
	private void cover_point(SVDBCoverpoint cp) throws SVParseException {
		cp.setTarget(parsers().exprParser().expression());
		
		if (fLexer.peekKeyword(KW.IFF)) {
			fLexer.eatToken();
			fLexer.readOperator(OP.LPAREN);
			cp.setIFF(parsers().exprParser().expression());
			fLexer.readOperator(OP.RPAREN);
		}
		
		if (fLexer.peekOperator(OP.LBRACE)) {
			fLexer.eatToken();
			while (fLexer.peek() != null && !fLexer.peekOperator(OP.RBRACE)) {
				if (isOption()) {
					cp.addItem(coverage_option());
				} else {
					boolean wildcard = fLexer.peekKeyword(KW.WILDCARD);
					if (wildcard) {
						fLexer.eatToken();
					}
					
					KW type = fLexer.readKeyword(KW.BINS, KW.ILLEGAL_BINS, KW.IGNORE_BINS);
					BinsKW kw = (type == KW.BINS)?BinsKW.Bins:
						(type == KW.ILLEGAL_BINS)?BinsKW.IllegalBins:BinsKW.IgnoreBins;
					String id = fLexer.readId();

					SVDBCoverpointBins bins = new SVDBCoverpointBins(wildcard, id, kw);

					boolean is_array = fLexer.peekOperator(OP.LBRACKET);
					bins.setIsArray(is_array);
					if (is_array) {
						fLexer.eatToken();
						if (fLexer.peekOperator(OP.RBRACKET)) {
							fLexer.eatToken();
						} else {
							bins.setArrayExpr(parsers().exprParser().expression());
							fLexer.readOperator(OP.RBRACKET);
						}
					}
					
					fLexer.readOperator(OP.EQ);
					
					if (fLexer.peekKeyword(KW.DEFAULT)) {
						// Some sort of default bin
						fLexer.eatToken();
						boolean is_sequence = fLexer.peekKeyword(KW.SEQUENCE);
						if (is_sequence) {
							fLexer.eatToken();
							bins.setBinsType(BinsType.DefaultSeq);
						} else {
							bins.setBinsType(BinsType.Default);
						}
					} else {
						if (fLexer.peekOperator(OP.LBRACE)) {
							List<SVDBExpr> l = new ArrayList<SVDBExpr>();
							bins.setBinsType(BinsType.OpenRangeList);
							// TODO:
							parsers().exprParser().open_range_list(l);
						} else if (fLexer.peekOperator(OP.LPAREN)) {
							bins.setBinsType(BinsType.TransList);
							// TODO:
							trans_list();
						} else {
							fLexer.readOperator(OP.LBRACE, OP.LPAREN);
						}
					}
					// Possible with ( with_covergroup_expression )
					if (fLexer.peekKeyword(KW.WITH)) {
						fLexer.eatToken();
						fLexer.readOperator(OP.LPAREN);
						bins.setWith(parsers().exprParser().expression());
						fLexer.readOperator(OP.RPAREN);
					}
					
					// Possible if (iff ( expression ))
					if (fLexer.peekKeyword(KW.IFF)) {
						fLexer.eatToken();
						fLexer.readOperator(OP.LPAREN);
						bins.setIFF(parsers().exprParser().expression());
						fLexer.readOperator(OP.RPAREN);
					}
					cp.addItem(bins);
					fLexer.readOperator(OP.SEMICOLON);
				}
			}
			fLexer.readOperator(OP.RBRACE);
		} else {
			fLexer.readOperator(OP.SEMICOLON);
		}
	}
	
	private void trans_list() throws SVParseException {
		
		while (fLexer.peek() != null) {
			fLexer.readOperator(OP.LPAREN);
			// TODO:
			trans_set();
			fLexer.readOperator(OP.RPAREN);
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
	}
	
	private void trans_set() throws SVParseException {
		// TODO:
		trans_range_list();
		
		while (fLexer.peekOperator(OP.EQ_GT)) {
			// TODO:
			fLexer.eatToken();
			trans_range_list();
		}
	}
	
	private void trans_range_list() throws SVParseException {
		// TODO:
		range_list();
		
		if (fLexer.peekOperator(OP.LBRACKET)) {
			fLexer.eatToken();
			// TODO:
			fLexer.readOperator(OP.MUL, OP.EQ, OP.IMPL);
			// TODO:
			repeat_range();
			fLexer.readOperator(OP.RBRACKET);
		}
	}
	
	private void range_list() throws SVParseException {
		// TODO:
		while (fLexer.peek() != null) {
			if (fLexer.peekOperator(OP.LBRACKET)) {
				fParsers.exprParser().parse_range();
			} else {
				fParsers.exprParser().expression();
			}
			
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
	}
	
	private void repeat_range() throws SVParseException {
		// TODO:
		fParsers.exprParser().expression();
		
		if (fLexer.peekOperator(OP.COLON)) {
			fLexer.eatToken();
			fParsers.exprParser().expression();
		}
	}
	
	private void cover_cross(SVDBCoverpointCross cp) throws SVParseException {
		while (fLexer.peek() != null) {
			SVDBIdentifierExpr id = fParsers.exprParser().idExpr();
			cp.getCoverpointList().add(id);
		
			if (fLexer.peekOperator(OP.COMMA)) {
				fLexer.eatToken();
			} else {
				break;
			}
		}
		
		if (fLexer.peekKeyword(KW.IFF)) {
			fLexer.eatToken();
			fLexer.readOperator(OP.LPAREN);
			cp.setIFF(parsers().exprParser().expression());
			fLexer.readOperator(OP.RPAREN);
		}
		
		if (fLexer.peekOperator(OP.LBRACE)) {
			fLexer.eatToken();
			while (fLexer.peek() != null && !fLexer.peekOperator(OP.RBRACE)) {
				if (isOption()) {
					cp.addItem(coverage_option());
				} else {
					SVDBCoverageCrossBinsSelectStmt select_stmt = new SVDBCoverageCrossBinsSelectStmt();
					KW type = fLexer.readKeyword(KW.BINS, KW.ILLEGAL_BINS, KW.IGNORE_BINS);
					select_stmt.setBinsType(type.getImg());
					select_stmt.setBinsName(fParsers.exprParser().idExpr());
					fLexer.readOperator(OP.EQ);
					
					if (fLexer.peekId()) {
						// ID with (expression)
						// TODO: save
						fLexer.eatToken();
						fLexer.readKeyword(KW.WITH);
						fLexer.readOperator(OP.LPAREN);
						fParsers.exprParser().expression();
						fLexer.readOperator(OP.RPAREN);
					} else {
						select_stmt.setSelectCondition(select_expression());
					}
					
					if (fLexer.peekKeyword(KW.IFF)) {
						fLexer.eatToken();
						fLexer.readOperator(OP.LPAREN);
						select_stmt.setIffExpr(fParsers.exprParser().expression());
						fLexer.readOperator(OP.RPAREN);
					}
					fLexer.readOperator(OP.SEMICOLON);
					cp.addItem(select_stmt);
				}
			}
			fLexer.readOperator(OP.RBRACE);
		} else {
			fLexer.readOperator(OP.SEMICOLON);
		}
	}
	
	private SVDBExpr select_expression() throws SVParseException {
		SVDBExpr expr = or_select_expression();
		
		return expr;
	}
	
	private SVDBExpr or_select_expression() throws SVParseException {
		SVDBExpr expr = and_select_expression();
		
		while (fLexer.peekOperator(OP.OR2)) {
			fLexer.eatToken();
			expr = new SVDBBinaryExpr(expr, "||", and_select_expression());
		}
		
		return expr;
	}
	
	private SVDBExpr and_select_expression() throws SVParseException {
		SVDBExpr expr = unary_select_condition();
		
		while (fLexer.peekOperator(OP.AND2)) {
			fLexer.eatToken();
			expr = new SVDBBinaryExpr(expr, "&&", unary_select_condition());
		}
	
		return expr;
	}
	
	private SVDBExpr unary_select_condition() throws SVParseException {
		if (fLexer.peekOperator(OP.NOT)) {
			return new SVDBUnaryExpr("!", select_condition());
		} else if (fLexer.peekOperator(OP.LPAREN)) {
			fLexer.eatToken();
			SVDBParenExpr ret = new SVDBParenExpr(select_expression());
			fLexer.readOperator(OP.RPAREN);
			return ret;
		} else {
			return select_condition();
		}
	}
	
	private SVDBExpr select_condition() throws SVParseException {
		long start = fLexer.getStartLocation();
		SVDBCrossBinsSelectConditionExpr select_c = new SVDBCrossBinsSelectConditionExpr();
		SVDBUnaryExpr not_expr = null;
		SVDBExpr bins_expr = null;
		select_c.setLocation(start);
		
		if(fLexer.peekOperator(OP.NOT)) {
			not_expr = new SVDBUnaryExpr("!", null);
			not_expr.setLocation(fLexer.getStartLocation());
			fLexer.eatToken();
		}
		
		fLexer.readKeyword(KW.BINSOF);
		fLexer.readOperator(OP.LPAREN);
		bins_expr = fParsers.exprParser().idExpr();
		if (fLexer.peekOperator(OP.DOT)) {
			fLexer.eatToken();
			bins_expr = new SVDBFieldAccessExpr(bins_expr, false, 
					fParsers.exprParser().idExpr());
		}
		
		if (fLexer.peekOperator(OP.LBRACKET)) {
			// TODO: capture
			fLexer.eatToken();
			fParsers.exprParser().expression();
			fLexer.readOperator(OP.RBRACKET);
		}

		if (not_expr != null) {
			not_expr.setExpr(bins_expr);
			select_c.setBinsExpr(not_expr);
		} else {
			select_c.setBinsExpr(bins_expr);
		}
		fLexer.readOperator(OP.RPAREN);
		
		if (fLexer.peekKeyword(KW.INTERSECT)) {
			fLexer.eatToken();
			fParsers.exprParser().open_range_list(select_c.getIntersectList());
		}
		
		return select_c;
	}
	
	private boolean isOption() throws SVParseException {
		if (fLexer.peekId()) {
			String id = fLexer.peek();
			return (id.equals("option") || id.equals("type_option"));
		} else {
			return false;
		}
	}
}
