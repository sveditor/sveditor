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


package net.sf.sveditor.core.db.expr;


public class SVExprIterator {
	
	public void visit(SVExpr expr) {
		switch (expr.getExprType()) {
			// Ignored expression elements
			case ArrayAccess: array_access((SVArrayAccessExpr)expr); break;
			case Assign: assign((SVAssignExpr)expr); break;
			case Cast: cast((SVCastExpr)expr); break;
			case DistList: dist_list((SVDistListExpr)expr); break;
			case Binary: binary_expr((SVBinaryExpr)expr); break;
			case Cond: cond((SVCondExpr)expr); break;
			
			case ConstraintIf: constraint_if((SVConstraintIfExpr)expr); break;
			case ConstraintSet: constraint_set((SVConstraintSetExpr)expr); break;
			case FieldAccess: field_access((SVFieldAccessExpr)expr); break;
			case Identifier: identifier((SVIdentifierExpr)expr); break;
			case Implication: implication((SVImplicationExpr)expr); break;
			case IncDec: inc_dec((SVIncDecExpr)expr); break;
			case Inside: inside((SVInsideExpr)expr); break;
			case Literal: literal((SVLiteralExpr)expr); break;
			case Paren: paren((SVParenExpr)expr); break;
			case QualifiedSuperFieldRef: qualified_super_field_ref((SVQualifiedSuperFieldRefExpr)expr); break;
			case QualifiedThisRef: qualified_this_ref((SVQualifiedThisRefExpr)expr); break;
			case SolveBefore: solve_before((SVSolveBeforeExpr)expr); break;
			case TFCall: tf_call((SVTFCallExpr)expr); break;
			case Unary: unary((SVUnaryExpr)expr); break;
			case Range: range((SVRangeExpr)expr); break;
			
			default:
				System.out.println("unhandled expression: " + expr.getExprType());
				break;
		}
	}
	
	protected void array_access(SVArrayAccessExpr expr) {
		visit(expr.getLhs());
	}
	
	protected void assign(SVAssignExpr expr) {
		visit(expr.getLhs());
		visit(expr.getRhs());
	}
	
	protected void binary_expr(SVBinaryExpr expr) {
		visit(expr.getLhs());
		visit(expr.getRhs());
	}
	
	protected void cast(SVCastExpr expr) {
		visit(expr.getExpr());
	}
	
	protected void cond(SVCondExpr expr) {
		visit(expr.getLhs());
		visit(expr.getMhs());
		visit(expr.getRhs());
	}
	
	protected void dist_item(SVDistItemExpr expr) {
	}
	
	protected void dist_list(SVDistListExpr expr) {
	}
	
	protected void constraint_if(SVConstraintIfExpr expr) {
		visit(expr.getExpr());
		visit(expr.getConstraint());
		if (expr.getElseClause() != null) {
			visit(expr.getElseClause());
		}
	}
	
	protected void constraint_set(SVConstraintSetExpr expr) {
		for (SVExpr e : expr.getConstraintList()) {
			visit(e);
		}
	}
	
	protected void field_access(SVFieldAccessExpr expr) {
		visit(expr.getExpr());
	}
	
	protected void identifier(SVIdentifierExpr expr) {
	}
	
	protected void implication(SVImplicationExpr expr) {
		visit(expr.getExpr());
		visit(expr.getConstraintSet());
	}
	
	protected void inc_dec(SVIncDecExpr expr) {
		visit(expr.getExpr());
	}
	
	protected void inside(SVInsideExpr expr) {
		visit(expr.getLhs());
		for (SVExpr e : expr.getValueRangeList()) {
			visit(e);
		}
	}
	
	protected void literal(SVLiteralExpr expr) {
	}
	
	protected void paren(SVParenExpr expr) {
		visit(expr.getExpr());
	}

	protected void qualified_super_field_ref(SVQualifiedSuperFieldRefExpr expr) {
		visit(expr.getLhs());
	}
	
	protected void qualified_this_ref(SVQualifiedThisRefExpr expr) {
		visit(expr.getExpr());
	}
	
	protected void solve_before(SVSolveBeforeExpr expr) {
	}
	
	protected void tf_call(SVTFCallExpr expr) {
		if (expr.getTarget() != null) {
			visit(expr.getTarget());
		}
	}
	
	protected void unary(SVUnaryExpr expr) {
		visit(expr.getExpr());
	}
	
	protected void range(SVRangeExpr expr) {
		visit(expr.getLeft());
		visit(expr.getRight());
	}
}
