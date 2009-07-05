package net.sf.sveditor.core.expr.parser;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

public class SVExprParser {
	private SVExprLexer						fLexer;
	private SVExprDump							fExprDump;
	private boolean								fDebugEn = false;
	
	public SVExprParser() {
		fLexer = new SVExprLexer();
		fExprDump = new SVExprDump(System.out);
	}
	

	/**
	 * parse_constraint()
	 * 
	 * Parse the body of a constraint statement
	 * 
	 * @param in
	 * @return
	 * @throws SVExprParseException
	 */
	public List<SVConstraintExpr> parse_constraint(InputStream in) throws SVExprParseException {
		fLexer.init(in);
		
		List<SVConstraintExpr> ret = new ArrayList<SVConstraintExpr>();

		try {
			SVExpr expr;
			
			while (!peek().equals("")) {
				debug("top of while: peek=" + peek());
				expr = constraint_block_item();
				
				if (expr != null) {
					ret.add((SVConstraintExpr)expr);
				} else {
					System.out.println("[FIXME] null expr");
				}
			}
		} catch (Exception e) {
			if (!(e instanceof EOFException)) {
				// Problem
				System.out.println("[ERROR] " + e.getMessage());
				throw new SVExprParseException(e);
			}
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
	public SVExpr parse_expression(InputStream in) throws SVExprParseException {
		fLexer.init(in);
		SVExpr expr = null;
		
		try {
			expr = expression();
		} catch (Exception e) {
			if (!(e instanceof EOFException)) {
				// Problem
				System.out.println("[ERROR] " + e.getMessage());
				throw new SVExprParseException(e);
			}
		}
		
		return expr;
	}
	
	public List<SVCoverageExpr> parse_coverpoint(InputStream in) throws SVExprParseException {
		return null;
	}
	
	public List<SVCoverageExpr> parse_covercross(InputStream in) throws SVExprParseException {
		return null;
	}
	
	
	/**
	 * p
	 * @return
	 * @throws SVExprParseException
	 * @throws SVExprLexerException
	 */
	
	public SVExpr constraint_block_item() throws SVExprParseException, SVExprLexerException {
		SVExpr ret = null;
		
		if (peekKeyword("solve")) {
			// TODO: do actual parse
			ret = solve_expression();
		} else {
			ret = constraint_expression();
		}
		
		return ret;
	}
	
	
	public SVExpr constraint_expression() throws SVExprParseException, SVExprLexerException {
		SVExpr ret = null;
		
		debug("--> constraint_expression()");
		
		if (peekKeyword("if")) {
			ret = constraint_if_expression();
		} else if (peekKeyword("foreach")) {
			// TODO:
			throw new SVExprParseException("foreach unhandled");
		} else {
			// Not sure. Possibly one of:
			// - expression_or_dist
			//     - expression [dist { dist_list }]
			// - expression -> constraint_set

			// tok = expression(tok);
			SVExpr expr = expression();
			
			fLexer.peek();
			
			if (fDebugEn) {
				System.out.print("expr=");
				fExprDump.dump(expr);
				System.out.println();
			}
			
			if (peekKeyword("dist")) {
				eatToken();

				// TODO: unimplemented
				System.out.println("[TODO] dist_list unimplemented");
				readOperator("{");
				SVDistListExpr dist = dist_list();
				readOperator("}");
				readOperator(";");
			} else if (peekOperator(";")) {
				// Done
				eatToken();
				ret = expr;
			} else if (peekOperator("->")) {
				eatToken();
				
				ret = new SVImplicationExpr(expr, constraint_set());
			} else {
				throw new SVExprParseException("Unknown suffix for expression: " + fLexer.getImage());
			}
		}
		
		debug("<-- constraint_expression()");
		
		return ret;
	}
	
	public SVDistListExpr dist_list() throws SVExprParseException, SVExprLexerException {
		SVDistItemExpr item = dist_item();
		
		while (peekOperator(",")) {
			eatToken();
			
			item = dist_item();
		}
		
		return null;
	}
	
	public SVDistItemExpr dist_item() throws SVExprParseException, SVExprLexerException {
	
		if (peekOperator("[")) {
			eatToken();
			SVExpr left = expression();
			readOperator(":");
			SVExpr right = expression();
			readOperator("]");
		} else {
			expression();
		}
		
		if (peekOperator(":=", ":/")) {
			eatToken();
			expression();
		}
		
		return null;
	}
	
	/**
	 * ConstraintIfExpression ::=
	 *     if ( expression ) ConstraintSet [else ConstraintSet]
	 * @return
	 * @throws SVExprParseException
	 * @throws SVExprLexerException
	 */
	public SVConstraintIfExpr constraint_if_expression() throws SVExprParseException, SVExprLexerException {
		SVConstraintIfExpr ret;
		debug("--> constraint_if_expression");
		
		eatToken(); // 'if'
		
		readOperator("(");
		SVExpr if_expr = expression();
		readOperator(")");
		
		SVConstraintSetExpr constraint = constraint_set();
		
		if (peekKeyword("else")) {
			eatToken();
			SVConstraintSetExpr else_expr = constraint_set();
			ret = new SVConstraintIfExpr(if_expr, constraint, else_expr);
		} else {
			ret = new SVConstraintIfExpr(if_expr, constraint, null);
		}
		
		debug("<-- constraint_if_expression");
		return ret;
	}
	
	public SVConstraintSetExpr constraint_set() throws SVExprParseException, SVExprLexerException {
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
	
	public SVExpr solve_expression() throws SVExprParseException, SVExprLexerException {
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
	 * Expression := AssignmentExpression
	 * @param tok
	 * @return
	 * @throws ConstraintException
	 */
	public SVExpr expression() throws SVExprParseException, SVExprLexerException {
		debug("--> expression()");
		SVExpr expr = assignmentExpression();
		debug("<-- expression() " + expr);
		return expr; 
	}
	
	/**
	 * AssignmentExpression :=
	 * 		ConditionalExpression [ AssignmentOperator AssignmentExpression]
	 * 
	 * @return
	 * @throws SVExprParseException
	 * @throws SVExprLexerException
	 */
	public SVExpr assignmentExpression() throws SVExprParseException, SVExprLexerException {
		debug("--> assignmentExpression()");
		SVExpr a = conditionalExpression();
		
		if (peekOperator("=", "+=", "-=", "*=", "/=", "&=", "|=", "^=", "%=", "<<=", ">>=")) {
			String op = readOperator();
			SVExpr rhs = assignmentExpression();
			a = new SVAssignExpr(a, op, rhs);
		} else if (peekKeyword("inside")) {
			eatToken();
			SVInsideExpr inside = new SVInsideExpr(a);
			readOperator("{");
			do {
				if (peekOperator(",")) {
					eatToken();
				}
				if (peekOperator("[")) {
					eatToken();
					SVExpr left = expression();
					readOperator(":");
					SVExpr right = expression();
					inside.getValueRangeList().add(new SVRangeExpr(left, right));
					readOperator("]");
				} else {
					inside.getValueRangeList().add(expression());
				}
			} while (peekOperator(","));
			readOperator("}");
			
			a = inside;
		}

		debug("<-- assignmentExpression() " + a);
		return a;
	}
	
	/**
	 * conditionalExpression ::=
	 *     conditionalOrExpression [ '?' Expression ':' ConditionalExpression]
	 * @return
	 * @throws SVExprParseException
	 * @throws SVExprLexerException
	 */
	public SVExpr conditionalExpression() throws SVExprParseException, SVExprLexerException {
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
	 * @throws SVExprParseException
	 * @throws SVExprLexerException
	 */
	public SVExpr conditionalOrExpression() throws SVExprParseException, SVExprLexerException {
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
	 * @throws SVExprParseException
	 * @throws SVExprLexerException
	 */
	public SVExpr conditionalAndExpression() throws SVExprParseException, SVExprLexerException {
		SVExpr a = inclusiveOrExpression();
		
		while (peekOperator("&&")) {
			eatToken();
			a = new SVBinaryExpr(a, "&&", inclusiveOrExpression());
		}
		return a;
	}
	
	public SVExpr inclusiveOrExpression() throws SVExprParseException, SVExprLexerException {
		SVExpr a = exclusiveOrExpression();
		
		while (peekOperator("|")) {
			eatToken();
			a = new SVBinaryExpr(a, "|", exclusiveOrExpression());
		}
		
		return a;
	}
	
	public SVExpr exclusiveOrExpression() throws SVExprParseException, SVExprLexerException {
		SVExpr a = andExpression();
		
		while (peekOperator("^")) {
			eatToken();
			a = new SVBinaryExpr(a, "^", andExpression());
		}
		
		return a;
	}
	
	public SVExpr andExpression() throws SVExprParseException, SVExprLexerException {
		SVExpr a = equalityExpression();
		
		while (peekOperator("&")) {
			eatToken();
			a = new SVBinaryExpr(a, "&", equalityExpression());
		}
		
		return a;
	}
	
	public SVExpr equalityExpression() throws SVExprParseException, SVExprLexerException {
		SVExpr a = relationalExpression();
		
		while (peekOperator("==", "!=")) {
			a = new SVBinaryExpr(a, readOperator(), relationalExpression());
		}
		
		return a;
	}
	
	public SVExpr relationalExpression() throws SVExprParseException, SVExprLexerException {
		SVExpr a = shiftExpression();
		
		while (peekOperator("<", ">", "<=", ">=")) {
			a = new SVBinaryExpr(a, readOperator(), shiftExpression());
		}
		
		return a;
	}
	
	public SVExpr shiftExpression() throws SVExprParseException, SVExprLexerException {
		SVExpr a = additiveExpression();
		
		while (peekOperator("<<", ">>", ">>>")) {
			a = new SVBinaryExpr(a, readOperator(), additiveExpression());
		}
		
		return a;
	}
	
	public SVExpr additiveExpression() throws SVExprParseException, SVExprLexerException {
		SVExpr a = multiplicativeExpression();
		
		while (peekOperator("+", "-")) {
			a = new SVBinaryExpr(a, readOperator(), multiplicativeExpression());
		}
		return a;
	}
	
	public SVExpr multiplicativeExpression() throws SVExprParseException, SVExprLexerException {
		SVExpr a = unaryExpression();
		
		while (peekOperator("*", "/", "%")) {
			a = new SVBinaryExpr(a, readOperator(), unaryExpression());
		}
		return a;
	}
	
	public SVExpr unaryExpression() throws SVExprParseException, SVExprLexerException {
		if (peekOperator("++", "--")) {
			return new SVIncDecExpr(readOperator(), unaryExpression());
		}
		
		if (peekOperator("+", "-", "~", "!", "|")) {
			return new SVUnaryExpr(readOperator(), unaryExpression());
		}
		
		SVExpr a = primary();
		
		while (peekOperator(".", "[")) {
			a = selector(a);
		}
		
		while (peekOperator("++", "--")) {
			a = new SVIncDecExpr(readOperator(), a);
		}
		
		return a;
	}
	
	public SVExpr primary() throws SVExprParseException, SVExprLexerException {
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
			} else if (fLexer.isIdentifier()) {
				debug("  primary \"" + fLexer.getImage() + "\" is identifier");
				String qi[] = qualifiedIdentifier();
				
				if (peekOperator("(")) {
					// Name arguments
					throw new SVExprParseException("Unhandled primary");
				} else if (false && peekOperator("[") /* && peekNextButOne().isOperator("]") */) {
					// Name '[]' { '[]' }
					System.out.println("primary [] returns null");
				} else {
					ret = new SVIdentifierExpr(qi);
					debug("  after id-read: " + peek());
					debug("  qi.length=" + qi.length);
				}
			} else if (peekKeyword("this")) {
				eatToken();
				
				if (peekOperator("(")) {
					// 'this' Arguments
					// Alternate constructor invocation
					// TODO: N/A??
				}
				throw new SVExprParseException("Unhandled primary 'this'");
			} else if (peekKeyword("super")) {
				throw new SVExprParseException("Unhandled primary 'super'");
			} else if (peekKeyword("void")) {
				eatToken();
			} else {
				throw new SVExprParseException("Unexpected token in primary: \"" + fLexer.getImage() + "\"");
			}
		}
		
		debug("<-- primary() " + ret);
		return ret;
	}
	
	public String [] qualifiedIdentifier() throws SVExprParseException, SVExprLexerException {
		if (!fLexer.isIdentifier()) {
			throw new SVExprParseException("Identifier Expected");
		}
		List<String> ret = new ArrayList<String>();
		
		ret.add(readIdentifier());
		while (peekOperator(".") /* && peekNextButOne().isIdentifier() */) {
			eatToken();
			ret.add(readIdentifier());
		}
		
		return ret.toArray(new String[ret.size()]);
	}
	
	public SVExpr [] arguments() throws SVExprParseException, SVExprLexerException {
		readOperator("(");
		
		if (peekOperator(")")) {
			eatToken();
			return new SVExpr[0];
		}
		
		SVExpr arguments[] = argumentList();
		readOperator(")");
		
		return arguments;
	}
	
	public SVExpr [] argumentList() throws SVExprParseException, SVExprLexerException {
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
	
	public SVExpr selector(SVExpr expr) throws SVExprParseException, SVExprLexerException {
		if (peekOperator(".")) {
			eatToken();
			
			fLexer.peek();
			if (fLexer.isIdentifier()) {
				String id = fLexer.readId();
				
				if (peekOperator("(")) {
					return new SVTFCallExpr(expr, id, arguments());
				}
				// '.' identifier
				return new SVFieldAccessExpr(expr, id);
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
			
			if (peekOperator(":")) {
				eatToken();
				high = expression();
			}
			
			readOperator("]");
			if (expr == null) {
				System.out.println("array expr == null");
			}
			return new SVArrayAccessExpr(expr, low, high);
		}
		
		throw new SVExprParseException("Unexpected token \"" + fLexer.getImage() + "\"");
	}
	
	private String peek() throws SVExprLexerException {
		return fLexer.peek();
	}

	private boolean peekOperator(String ... ops) throws SVExprLexerException {
		return fLexer.peekOperator(ops);
	}
	
	private String readOperator(String ... ops) throws SVExprLexerException {
		return fLexer.readOperator(ops);
	}
	
	private boolean peekKeyword(String ... kw) throws SVExprLexerException {
		return fLexer.peekKeyword(kw);
	}
	
	private String readKeyword(String ... kw) throws SVExprLexerException {
		return fLexer.readKeyword(kw);
	}
	
	private String readIdentifier() throws SVExprLexerException {
		return fLexer.readId();
	}
	
	private String readNumber() throws SVExprLexerException {
		return fLexer.readNumber();
	}
	
	private void eatToken() {
		fLexer.eatToken();
	}
	
	private void debug(String msg) {
		if (fDebugEn) {
			System.out.println(msg);
		}
	}
}
