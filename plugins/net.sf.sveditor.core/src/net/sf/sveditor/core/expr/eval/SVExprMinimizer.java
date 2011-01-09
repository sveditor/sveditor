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


package net.sf.sveditor.core.expr.eval;

import net.sf.sveditor.core.db.expr.SVArrayAccessExpr;
import net.sf.sveditor.core.db.expr.SVAssignExpr;
import net.sf.sveditor.core.db.expr.SVBinaryExpr;
import net.sf.sveditor.core.db.expr.SVCastExpr;
import net.sf.sveditor.core.db.expr.SVCondExpr;
import net.sf.sveditor.core.db.expr.SVConstraintIfExpr;
import net.sf.sveditor.core.db.expr.SVConstraintSetExpr;
import net.sf.sveditor.core.db.expr.SVDistItemExpr;
import net.sf.sveditor.core.db.expr.SVDistListExpr;
import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.expr.SVFieldAccessExpr;
import net.sf.sveditor.core.db.expr.SVIdentifierExpr;
import net.sf.sveditor.core.db.expr.SVImplicationExpr;
import net.sf.sveditor.core.db.expr.SVIncDecExpr;
import net.sf.sveditor.core.db.expr.SVInsideExpr;
import net.sf.sveditor.core.db.expr.SVLiteralExpr;
import net.sf.sveditor.core.db.expr.SVParenExpr;
import net.sf.sveditor.core.db.expr.SVQualifiedSuperFieldRefExpr;
import net.sf.sveditor.core.db.expr.SVQualifiedThisRefExpr;
import net.sf.sveditor.core.db.expr.SVRangeExpr;
import net.sf.sveditor.core.db.expr.SVSolveBeforeExpr;
import net.sf.sveditor.core.db.expr.SVTFCallExpr;
import net.sf.sveditor.core.db.expr.SVUnaryExpr;

public class SVExprMinimizer {
	
	
	public SVExpr minimize(SVExpr expr) {
		SVExpr ret = (SVExpr)expr.duplicate();
		
		
		
		return ret;
	}
	
	private SVExpr minimize_i(SVExpr expr) {
		switch (expr.getExprType()) {
		// Ignored expression elements
		case ArrayAccess: expr = array_access((SVArrayAccessExpr)expr); break;
		case Assign: expr = assign((SVAssignExpr)expr); break;
		case Cast: expr = cast((SVCastExpr)expr); break;
		case DistList: expr = dist_list((SVDistListExpr)expr); break;
		case Binary: expr = binary_expr((SVBinaryExpr)expr); break;
		case Cond: expr = cond((SVCondExpr)expr); break;
		
		case ConstraintIf: expr = constraint_if((SVConstraintIfExpr)expr); break;
		case ConstraintSet: expr = constraint_set((SVConstraintSetExpr)expr); break;
		case FieldAccess: expr = field_access((SVFieldAccessExpr)expr); break;
		case Identifier: expr = identifier((SVIdentifierExpr)expr); break;
		case Implication: expr = implication((SVImplicationExpr)expr); break;
		case IncDec: expr = inc_dec((SVIncDecExpr)expr); break;
		case Inside: expr = inside((SVInsideExpr)expr); break;
		case Literal: expr = literal((SVLiteralExpr)expr); break;
		case Paren: expr = paren((SVParenExpr)expr); break;
		case QualifiedSuperFieldRef: expr = qualified_super_field_ref((SVQualifiedSuperFieldRefExpr)expr); break;
		case QualifiedThisRef: expr = qualified_this_ref((SVQualifiedThisRefExpr)expr); break;
		case SolveBefore: expr = solve_before((SVSolveBeforeExpr)expr); break;
		case TFCall: expr = tf_call((SVTFCallExpr)expr); break;
		case Unary: expr = unary((SVUnaryExpr)expr); break;
		case Range: expr = range((SVRangeExpr)expr); break;
	
		default:
			System.out.println("unhandled expression: " + expr.getExprType());
			break;
		}
		
		return expr;
	}

	protected SVExpr array_access(SVArrayAccessExpr expr) {
		return minimize_i(expr.getLhs());
	}
	
	protected SVExpr assign(SVAssignExpr expr) {
		expr.setLhs(minimize_i(expr.getLhs()));
		expr.setRhs(minimize_i(expr.getRhs()));
		
		return expr;
	}
	
	protected SVExpr binary_expr(SVBinaryExpr expr) {
		minimize_i(expr.getLhs());
		minimize_i(expr.getRhs());
		
		return expr;
	}
	
	protected SVExpr cast(SVCastExpr expr) {
		minimize_i(expr.getExpr());
		
		return expr;
	}
	
	protected SVExpr cond(SVCondExpr expr) {
		minimize_i(expr.getLhs());
		minimize_i(expr.getMhs());
		minimize_i(expr.getRhs());
		
		return expr;
	}
	
	protected SVExpr dist_item(SVDistItemExpr expr) {
		return expr;
	}
	
	protected SVExpr dist_list(SVDistListExpr expr) {
		return expr;
	}
	
	protected SVExpr constraint_if(SVConstraintIfExpr expr) {
		minimize_i(expr.getExpr());
		minimize_i(expr.getConstraint());
		if (expr.getElseClause() != null) {
			minimize_i(expr.getElseClause());
		}
		
		return expr;
	}
	
	protected SVExpr constraint_set(SVConstraintSetExpr expr) {
		for (SVExpr e : expr.getConstraintList()) {
			minimize_i(e);
		}
		
		return expr;
	}
	
	protected SVExpr field_access(SVFieldAccessExpr expr) {
		minimize_i(expr.getExpr());
		
		return expr;
	}
	
	protected SVExpr identifier(SVIdentifierExpr expr) {
		return expr;
	}
	
	protected SVExpr implication(SVImplicationExpr expr) {
		minimize_i(expr.getExpr());
		minimize_i(expr.getConstraintSet());
		
		return expr;
	}
	
	protected SVExpr inc_dec(SVIncDecExpr expr) {
		minimize_i(expr.getExpr());
		
		return expr;
	}
	
	protected SVExpr inside(SVInsideExpr expr) {
		minimize_i(expr.getLhs());
		for (SVExpr e : expr.getValueRangeList()) {
			minimize_i(e);
		}
		
		return expr;
	}
	
	protected SVExpr literal(SVLiteralExpr expr) {
		return expr;
	}
	
	protected SVExpr paren(SVParenExpr expr) {
		minimize_i(expr.getExpr());
		
		return expr;
	}

	protected SVExpr qualified_super_field_ref(SVQualifiedSuperFieldRefExpr expr) {
		minimize_i(expr.getLhs());
		
		return expr;
	}
	
	protected SVExpr qualified_this_ref(SVQualifiedThisRefExpr expr) {
		minimize_i(expr.getExpr());
		
		return expr;
	}
	
	protected SVExpr solve_before(SVSolveBeforeExpr expr) {
		return expr;
	}
	
	protected SVExpr tf_call(SVTFCallExpr expr) {
		if (expr.getTarget() != null) {
			minimize_i(expr.getTarget());
		}
		
		return expr;
	}
	
	protected SVExpr unary(SVUnaryExpr expr) {
		minimize_i(expr.getExpr());
		
		return expr;
	}
	
	protected SVExpr range(SVRangeExpr expr) {
		minimize_i(expr.getLeft());
		minimize_i(expr.getRight());
		
		return expr;
	}

}
