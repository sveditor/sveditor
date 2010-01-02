package net.sf.sveditor.core.expr.eval;

import java.math.BigInteger;

import net.sf.sveditor.core.expr.parser.SVBinaryExpr;
import net.sf.sveditor.core.expr.parser.SVExpr;
import net.sf.sveditor.core.expr.parser.SVIdentifierExpr;
import net.sf.sveditor.core.expr.parser.SVLiteralExpr;

public class SVIntegerExprEvaluator {
	private IValueProvider			fValueProvider;
	
	public SVIntegerExprEvaluator(IValueProvider provider) {
		fValueProvider = provider;
	}
	
	public BigInteger evaluate(SVExpr expr) throws Exception {
		switch (expr.getType()) {
			case Literal: {
				SVLiteralExpr literal = (SVLiteralExpr)expr;
				return parse_literal(literal);
				}
			
			case Binary: {
				SVBinaryExpr binary = (SVBinaryExpr)expr;
				return evaluate_binary(
						evaluate(binary.getLhs()), 
						binary.getOp(),
						evaluate(binary.getRhs()));
			}
			
			case Identifier: {
				SVIdentifierExpr id = (SVIdentifierExpr)expr;
				
				if (fValueProvider != null) {
					return fValueProvider.get_value(id.getIdStr());
				} else {
					throw new Exception("Unable to resolve value of id \"" + 
							id.getIdStr() + "\"; ValueProvider is null");
				}
			}
				
			default:
				throw new Exception("Unhandled expression type: " + expr.getType());
		}
	}
	
	public BigInteger parse_literal(SVLiteralExpr literal) throws Exception {
		int radix = 10;
		
		String value = literal.getValue();

		if (value.indexOf('\'') != -1) {
			int ind = value.indexOf('\'');
			// The previous character defines the radix
			int radix_c = Character.toLowerCase(value.charAt(ind-1));
			
			value = value.substring(ind+1);
			
			if (radix_c == 'b') {
				radix = 2;
			} else if (radix_c == 'd') {
				radix = 10;
			} else if (radix_c == 'h') {
				radix = 16;
			} else if (radix_c == 'o') {
				radix = 8;
			} else {
				throw new Exception("Unknown radix \"" + (char)radix_c + 
						"\" in literal \"" + literal.getValue() + "\"");
			}
		}
		
		return new BigInteger(value, radix);
	}
	
	public BigInteger evaluate_binary(
			BigInteger			lhs,
			String				op,
			BigInteger			rhs) throws Exception {
		if (op.equals("+")) {
			return lhs.add(rhs);
		} else if (op.equals("-")) {
			return lhs.subtract(rhs);
		} else if (op.equals("*")) {
			return lhs.multiply(rhs);
		} else {
			throw new Exception("Unsupported binary operator \"" + op + "\"");
		}
	}

}
