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


package org.sveditor.core.expr.eval;

import java.math.BigInteger;

import org.sveditor.core.db.expr.SVDBBinaryExpr;
import org.sveditor.core.db.expr.SVDBExpr;
import org.sveditor.core.db.expr.SVDBIdentifierExpr;
import org.sveditor.core.db.expr.SVDBLiteralExpr;

public class SVIntegerExprEvaluator {
	private IValueProvider			fValueProvider;
	
	public SVIntegerExprEvaluator(IValueProvider provider) {
		fValueProvider = provider;
	}
	
	public BigInteger evaluate(SVDBExpr expr) throws Exception {
		switch (expr.getType()) {
			case LiteralExpr: {
				SVDBLiteralExpr literal = (SVDBLiteralExpr)expr;
				return parse_literal(literal);
				}
			
			case BinaryExpr: {
				SVDBBinaryExpr binary = (SVDBBinaryExpr)expr;
				return evaluate_binary(
						evaluate(binary.getLhs()), 
						binary.getOp(),
						evaluate(binary.getRhs()));
			}
			
			case IdentifierExpr: {
				SVDBIdentifierExpr id = (SVDBIdentifierExpr)expr;
				
				if (fValueProvider != null) {
					return fValueProvider.get_value(id.getId());
				} else {
					throw new Exception("Unable to resolve value of id \"" + 
							id.getId() + "\"; ValueProvider is null");
				}
			}
				
			default:
				throw new Exception("Unhandled expression type: " + expr.getType());
		}
	}
	
	public BigInteger parse_literal(SVDBLiteralExpr literal) throws Exception {
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
