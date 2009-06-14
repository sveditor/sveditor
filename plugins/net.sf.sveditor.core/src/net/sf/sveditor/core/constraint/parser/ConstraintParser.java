package net.sf.sveditor.core.constraint.parser;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

public class ConstraintParser {
	private IConstraintParserObserver			fObserver;
	private ConstraintLexer						fLexer;
	private List<SVConstraintExpr>				fConstraints;
	
	public ConstraintParser() {
		fConstraints = new ArrayList<SVConstraintExpr>();
		fLexer = new ConstraintLexer();
	}
	
	
	public List<SVConstraintExpr> parse(InputStream in) throws ParseException {
		fLexer.init(in);
		
		fConstraints.clear();

		try {
			while (true) {
				if (peekKeyword("solve")) {
				
				} else {
					constraint_expression();
				}
			} 
		} catch (Exception e) {
			if (!(e instanceof EOFException)) {
				// Problem
				System.out.println("[ERROR] " + e.getMessage());
				throw new ParseException(e);
			}
		}
		
		return fConstraints;
	}
	
	public SVConstraintExpr constraint_expression() throws ParseException, LexerException {
		
		if (peekKeyword("if")) {
			// TODO:
		} else if (peekKeyword("foreach")) {
			// TODO:
		} else {
			// Not sure. Possibly one of:
			// - expression_or_dist
			//     - expression [dist { dist_list }]
			// - expression -> constraint_set

			// tok = expression(tok);
			SVExpr expr = expression();
			
			debug("expr=" + expr);
			
			if (peekKeyword("dist")) {
				eatToken();
				// It's the first
				throw new ParseException("Distributions not supported yet");
			} else if (peekKeyword("inside")) {
				// TODO: handle inside
			} else if (peekOperator("->")) {
				eatToken();
				
				// It's the second
				throw new ParseException("Implication not supported yet");
			} else {
				throw new ParseException("Unknown suffix for expression: " + fLexer.getImage());
			}
		}
		
		return null;
	}
	
	/**
	 * Expression := AssignmentExpression
	 * @param tok
	 * @return
	 * @throws ConstraintException
	 */
	public SVExpr expression() throws ParseException, LexerException {
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
	 * @throws ParseException
	 * @throws LexerException
	 */
	public SVExpr assignmentExpression() throws ParseException, LexerException {
		debug("--> assignmentExpression()");
		SVExpr a = conditionalExpression();
		
		if (peekOperator("=", "+=", "-=", "*=", "/=", "&=", "|=", "^=", "%=", "<<=", ">>=")) {
			String op = readOperator();
			SVExpr rhs = assignmentExpression();
			a = new SVAssignExpr(a, op, rhs);
		}

		debug("<-- assignmentExpression() " + a);
		return a;
	}
	
	/**
	 * conditionalExpression ::=
	 *     conditionalOrExpression [ '?' Expression ':' ConditionalExpression]
	 * @return
	 * @throws ParseException
	 * @throws LexerException
	 */
	public SVExpr conditionalExpression() throws ParseException, LexerException {
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
	 * @throws ParseException
	 * @throws LexerException
	 */
	public SVExpr conditionalOrExpression() throws ParseException, LexerException {
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
	 * @throws ParseException
	 * @throws LexerException
	 */
	public SVExpr conditionalAndExpression() throws ParseException, LexerException {
		SVExpr a = inclusiveOrExpression();
		
		while (peekOperator("&&")) {
			eatToken();
			a = new SVBinaryExpr(a, "&&", inclusiveOrExpression());
		}
		return a;
	}
	
	public SVExpr inclusiveOrExpression() throws ParseException, LexerException {
		SVExpr a = exclusiveOrExpression();
		
		while (peekOperator("|")) {
			eatToken();
			a = new SVBinaryExpr(a, "|", exclusiveOrExpression());
		}
		
		return a;
	}
	
	public SVExpr exclusiveOrExpression() throws ParseException, LexerException {
		SVExpr a = andExpression();
		
		while (peekOperator("^")) {
			eatToken();
			a = new SVBinaryExpr(a, "^", andExpression());
		}
		
		return a;
	}
	
	public SVExpr andExpression() throws ParseException, LexerException {
		SVExpr a = equalityExpression();
		
		while (peekOperator("&")) {
			eatToken();
			a = new SVBinaryExpr(a, "&", equalityExpression());
		}
		
		return a;
	}
	
	public SVExpr equalityExpression() throws ParseException, LexerException {
		SVExpr a = relationalExpression();
		
		while (peekOperator("==", "!=")) {
			a = new SVBinaryExpr(a, readOperator(), relationalExpression());
		}
		
		return a;
	}
	
	public SVExpr relationalExpression() throws ParseException, LexerException {
		SVExpr a = shiftExpression();
		
		for (;;) {
			if (peekOperator("<", ">", "<=", ">=")) {
				a = new SVBinaryExpr(a, readOperator(), shiftExpression());
			} else {
				break;
			}
		}
		
		return a;
	}
	
	public SVExpr shiftExpression() throws ParseException, LexerException {
		SVExpr a = additiveExpression();
		
		while (peekOperator("<<", ">>", ">>>")) {
			a = new SVBinaryExpr(a, readOperator(), additiveExpression());
		}
		
		return a;
	}
	
	public SVExpr additiveExpression() throws ParseException, LexerException {
		SVExpr a = multiplicativeExpression();
		
		while (peekOperator("+", "-")) {
			a = new SVBinaryExpr(a, readOperator(), multiplicativeExpression());
		}
		return a;
	}
	
	public SVExpr multiplicativeExpression() throws ParseException, LexerException {
		SVExpr a = unaryExpression();
		
		while (peekOperator("*", "/", "%")) {
			a = new SVBinaryExpr(a, readOperator(), unaryExpression());
		}
		return a;
	}
	
	public SVExpr unaryExpression() throws ParseException, LexerException {
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
	
	public SVExpr primary() throws ParseException, LexerException {
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
				debug("  primary is identifier");
				String qi[] = qualifiedIdentifier();
				
				if (peekOperator("(")) {
					// Name arguments
					throw new ParseException("Unhandled primary");
				} else if (peekOperator("[") /* && peekNextButOne().isOperator("]") */) {
					// Name '[]' { '[]' }
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
				throw new ParseException("Unhandled primary 'this'");
			} else if (peekKeyword("super")) {
				throw new ParseException("Unhandled primary 'super'");
			} else if (peekKeyword("void")) {
				eatToken();
			} else {
				throw new ParseException("Unexpected token in primary: \"" + fLexer.getImage() + "\"");
			}
		}
		
		debug("<-- primary() " + ret);
		return ret;
	}
	
	public String [] qualifiedIdentifier() throws ParseException, LexerException {
		if (!fLexer.isIdentifier()) {
			throw new ParseException("Identifier Expected");
		}
		List<String> ret = new ArrayList<String>();
		
		ret.add(readIdentifier());
		while (peekOperator(".") /* && peekNextButOne().isIdentifier() */) {
			eatToken();
			ret.add(readIdentifier());
		}
		
		return ret.toArray(new String[ret.size()]);
	}
	
	public SVExpr [] arguments() throws ParseException, LexerException {
		readOperator("(");
		
		if (peekOperator(")")) {
			eatToken();
			return new SVExpr[0];
		}
		
		SVExpr arguments[] = argumentList();
		readOperator(")");
		
		return arguments;
	}
	
	public SVExpr [] argumentList() throws ParseException, LexerException {
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
	
	public SVExpr selector(SVExpr expr) throws ParseException, LexerException {
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
			SVExpr index = expression();
			readOperator("]");
			return new SVArrayAccessExpr(expr, index);
		}
		
		throw new ParseException("Unexpected token \"" + fLexer.getImage() + "\"");
	}
	
	/*
	public ConstraintToken constraint_solve(ConstraintToken tok) {
		
		return tok;
	}
	 */
	
	private String peek() throws LexerException {
		return fLexer.peek();
	}

	private boolean peekOperator(String ... ops) throws LexerException {
		return fLexer.peekOperator(ops);
	}
	
	private String readOperator(String ... ops) throws LexerException {
		return fLexer.readOperator(ops);
	}
	
	private boolean peekKeyword(String ... kw) throws LexerException {
		return fLexer.peekKeyword(kw);
	}
	
	private String readKeyword(String ... kw) throws LexerException {
		return fLexer.readKeyword(kw);
	}
	
	private String readIdentifier() throws LexerException {
		return fLexer.readId();
	}
	
	private String readNumber() throws LexerException {
		return fLexer.readNumber();
	}
	
	private void eatToken() {
		fLexer.eatToken();
	}
	
	private void debug(String msg) {
		System.out.println(msg);
	}
}
