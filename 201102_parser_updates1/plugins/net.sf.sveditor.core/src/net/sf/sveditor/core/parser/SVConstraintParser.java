package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.expr.SVLiteralExpr;
import net.sf.sveditor.core.db.stmt.SVDBConstraintDistItemStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintDistListStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintForeachStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintIfStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintImplStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintSetStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintSolveBeforeStmt;
import net.sf.sveditor.core.db.stmt.SVDBExprStmt;
import net.sf.sveditor.core.db.stmt.SVDBStmt;

public class SVConstraintParser extends SVParserBase {
	
	public SVConstraintParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBConstraint parse(int qualifiers) throws SVParseException {
		SVDBConstraint c = new SVDBConstraint();
		// TODO: handle extern constraints
		c.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword("constraint");
		
		c.setName(fLexer.readId());
		
		fLexer.readOperator("{");
		
		while (fLexer.peek() != null && !fLexer.peekOperator("}")) {
			c.addConstraint(constraint_set_item());
		}
		
		fLexer.readOperator("}");
		
		return c;
	}
	
	public SVDBStmt constraint_set(boolean force_braces) throws SVParseException {
		debug("--> constraint_set()");
		
		if (force_braces || fLexer.peekOperator("{")) {
			SVDBConstraintSetStmt ret = new SVDBConstraintSetStmt(); 
			fLexer.readOperator("{");
			while (lexer().peek() != null && !fLexer.peekOperator("}")) {
				SVDBStmt c_stmt = constraint_set_item();
				ret.addConstraintStmt(c_stmt);
			}
			fLexer.readOperator("}");
			debug("<-- constraint_set()");
			return ret;
		} else {
			debug("<-- constraint_set()");
			return constraint_set_item();
		}
	}

	private SVDBStmt constraint_set_item() throws SVParseException {
		SVDBStmt ret = null;
		
		if (fLexer.peekKeyword("solve")) {
			ret = solve_expression();
		} else if (fLexer.peekKeyword("if")) {
			ret = constraint_if_expression();
		} else if (fLexer.peekKeyword("foreach")) {
			ret = constraint_foreach();
		} else {
			// Not sure. Possibly one of:
			// - expression_or_dist
			//     - expression [dist { dist_list }]
			// - expression -> constraint_set

			// tok = expression(tok);
			SVExpr expr = fParsers.exprParser().expression();
			
			if (fLexer.peekKeyword("dist")) {
				SVDBConstraintDistListStmt dist_stmt = new SVDBConstraintDistListStmt();
				fLexer.eatToken();
				dist_list(dist_stmt);
				fLexer.readOperator(";");
				
				ret = dist_stmt;
			} else if (fLexer.peekOperator(";")) {
				// Done
				fLexer.eatToken();
				ret = new SVDBExprStmt(expr);
			} else if (fLexer.peekOperator("->")) {
				fLexer.eatToken();
				
				ret = new SVDBConstraintImplStmt(expr, constraint_set(false));
			} else {
				error("Unknown suffix for expression: " + fLexer.getImage());
			}
		}
		
		return ret;
	}

	private void dist_list(SVDBConstraintDistListStmt dist_stmt) throws SVParseException {
		fLexer.readOperator("{");
		SVDBConstraintDistItemStmt item = dist_item();
		dist_stmt.addDistItem(item);

		while (fLexer.peekOperator(",")) {
			fLexer.eatToken();
			
			item = dist_item();
		}
		fLexer.readOperator("}");
	}

	private SVDBConstraintDistItemStmt dist_item() throws SVParseException {
		SVDBConstraintDistItemStmt ret = new SVDBConstraintDistItemStmt();
	
		if (fLexer.peekOperator("[")) {
			ret.setLHS(fParsers.exprParser().parse_range());
		} else {
			ret.setLHS(fParsers.exprParser().expression());
		}

		if (fLexer.peekOperator(",", "}")) {
			ret.setIsDist(false);
			ret.setRHS(new SVLiteralExpr("1"));
		} else {
			String type = fLexer.readOperator(":=", ":/");
			ret.setIsDist(type.equals(":/"));
			ret.setRHS(fParsers.exprParser().expression());
		}

		return ret;
	}

	private SVDBConstraintIfStmt constraint_if_expression() throws SVParseException {
		SVDBConstraintIfStmt ret;
		debug("--> constraint_if_expression");
		
		fLexer.eatToken(); // 'if'
		
		fLexer.readOperator("(");
		SVExpr if_expr = fParsers.exprParser().expression();
		fLexer.readOperator(")");
		
		SVDBStmt constraint = constraint_set(false);
		
		if (fLexer.peekKeyword("else")) {
			SVDBStmt else_stmt;
			fLexer.eatToken();
			if (fLexer.peekKeyword("if")) {
				else_stmt = constraint_if_expression();
			} else {
				else_stmt = constraint_set(false);
			}
			ret = new SVDBConstraintIfStmt(if_expr, constraint, else_stmt, true);
		} else {
			ret = new SVDBConstraintIfStmt(if_expr, constraint, null, false);
		}
		
		debug("<-- constraint_if_expression");
		return ret;
	}
	
	private SVDBStmt constraint_foreach() throws SVParseException {
		SVDBConstraintForeachStmt stmt = new SVDBConstraintForeachStmt();
		stmt.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword("foreach");
		
		fLexer.readOperator("(");
		stmt.setExpr(fParsers.exprParser().variable_lvalue());
		fLexer.readOperator(")");
		
		stmt.setStmt(constraint_set(false));
		
		return stmt;
	}
	
	private SVDBConstraintSolveBeforeStmt solve_expression() throws SVParseException {
		SVDBConstraintSolveBeforeStmt ret = new SVDBConstraintSolveBeforeStmt();
		fLexer.eatToken();
		
		// solve <var> {, <var>} ...
		SVExpr expr = fParsers.exprParser().variable_lvalue();
		ret.addSolveBefore(expr);
		
		while (fLexer.peekOperator(",")) {
			fLexer.eatToken(); // ,
			ret.addSolveBefore(fParsers.exprParser().variable_lvalue());
		}
		
		// solve <var> before ...
		fLexer.readKeyword("before");
		
		ret.addSolveAfter(fParsers.exprParser().variable_lvalue());
		
		while (fLexer.peekOperator(",")) {
			fLexer.eatToken(); // ,
			ret.addSolveAfter(fParsers.exprParser().variable_lvalue());
		}
		
		fLexer.readOperator(";");
		
		return ret;
	}
	

}
