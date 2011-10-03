package net.sf.sveditor.core.parser;

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.db.expr.SVDBBinaryExpr;
import net.sf.sveditor.core.db.expr.SVDBExpr;
import net.sf.sveditor.core.db.expr.SVDBParenExpr;
import net.sf.sveditor.core.db.expr.SVDBPropertySpecExpr;

public class SVPropertyExprParser extends SVParserBase {
	
	public SVPropertyExprParser(ISVParser parser) {
		super(parser);
	}
	
	private static final Set<String> BinaryOpKW;
	private static final Set<String> BinaryOp;
	
	static {
		BinaryOpKW = new HashSet<String>();
		BinaryOpKW.add("or");
		BinaryOpKW.add("and");
		BinaryOpKW.add("until");
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
	}
	
	public SVDBExpr property_expression() throws SVParseException {
		SVDBExpr ret = null;
		if (fLexer.peekKeyword("strong","weak")) {
			// weak_strong_expr
		} else if (fLexer.peekOperator("(")) {
			fLexer.eatToken();
			ret = new SVDBParenExpr(property_expression());
			fLexer.readOperator(")");
		} else if (fLexer.peekKeyword("not")) {
			// not expression
		} else if (fLexer.peekKeyword("nexttime", "s_nexttime")) {
			// nexttime expression
		} else if (fLexer.peekKeyword("always", "s_always", "eventually", "s_eventually")) {
			// always/eventually expression
		} else if (fLexer.peekKeyword("accept_on", "reject_on", "sync_accept_on", "sync_reject_on")) {
			// 
		} else {
			// TODO: property_statement, property_instance, clocking_event
			ret = sequence_expression();
		}
		
		// Now, parse binary operators
		if (fLexer.peekKeyword(BinaryOpKW) || fLexer.peekOperator(BinaryOp)) {
			String op = fLexer.eatToken();
			ret = new SVDBBinaryExpr(ret, op, property_expression());
		}
		
		return ret;
	}
	
	public SVDBExpr sequence_expression() throws SVParseException {
		SVDBExpr expr = null;
		if (fLexer.peekOperator("##")) {
		} else if (fLexer.peekOperator("@")) {
			SVDBExpr clk = fParsers.exprParser().clocking_event();
			expr = fParsers.exprParser().event_expression();
		} else if (fLexer.peekOperator("(")) {
			// ( sequence_expr {, sequence_match_item} ) [sequence_abbrev]
		} else {
			// sequence_or_dist
			expr = fParsers.exprParser().event_expression();
		}
		// TODO:
		
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
			expr.setDisableExpr(fParsers.exprParser().event_expression());
			fLexer.readOperator(")");
		}
		expr.setExpr(fParsers.propertyExprParser().property_expression());
		
		return expr;
	}
}
