/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.expr;

import net.sf.sveditor.core.db.stmt.SVDBConstraintDistListItem;
import net.sf.sveditor.core.db.stmt.SVDBConstraintDistListStmt;
import net.sf.sveditor.core.db.stmt.SVDBConstraintSolveBeforeStmt;


public class SVExprIterator {
	
	public void visit(SVDBExpr expr) {
		switch (expr.getType()) {
			// Ignored expression elements
			case ArrayAccessExpr: array_access((SVDBArrayAccessExpr)expr); break;
			case AssignExpr: assign((SVDBAssignExpr)expr); break;
			case CastExpr: cast((SVDBCastExpr)expr); break;
			case BinaryExpr: binary_expr((SVDBBinaryExpr)expr); break;
			case CondExpr: cond((SVDBCondExpr)expr); break;
			
			case FieldAccessExpr: field_access((SVDBFieldAccessExpr)expr); break;
			case IdentifierExpr: identifier((SVDBIdentifierExpr)expr); break;
			case IncDecExpr: inc_dec((SVDBIncDecExpr)expr); break;
			case InsideExpr: inside((SVDBInsideExpr)expr); break;
			case LiteralExpr: literal((SVDBLiteralExpr)expr); break;
			case ParenExpr: paren((SVDBParenExpr)expr); break;
			case TFCallExpr: tf_call((SVDBTFCallExpr)expr); break;
			case UnaryExpr: unary((SVDBUnaryExpr)expr); break;
			case RangeExpr: range((SVDBRangeExpr)expr); break;
			
			default:
				System.out.println("unhandled expression: " + expr.getType());
				break;
		}
	}
	
	protected void array_access(SVDBArrayAccessExpr expr) {
		visit(expr.getLhs());
	}
	
	protected void assign(SVDBAssignExpr expr) {
		visit(expr.getLhs());
		visit(expr.getRhs());
	}
	
	protected void binary_expr(SVDBBinaryExpr expr) {
		visit(expr.getLhs());
		visit(expr.getRhs());
	}
	
	protected void cast(SVDBCastExpr expr) {
		visit(expr.getExpr());
	}
	
	protected void cond(SVDBCondExpr expr) {
		visit(expr.getLhs());
		visit(expr.getMhs());
		visit(expr.getRhs());
	}
	
	protected void dist_item(SVDBConstraintDistListItem expr) {
	}
	
	protected void dist_list(SVDBConstraintDistListStmt expr) {
	}
	
	protected void field_access(SVDBFieldAccessExpr expr) {
		visit(expr.getExpr());
	}
	
	protected void identifier(SVDBIdentifierExpr expr) {
	}
	
	protected void inc_dec(SVDBIncDecExpr expr) {
		visit(expr.getExpr());
	}
	
	protected void inside(SVDBInsideExpr expr) {
		visit(expr.getLhs());
		for (SVDBExpr e : expr.getValueRangeList()) {
			visit(e);
		}
	}
	
	protected void literal(SVDBLiteralExpr expr) {
	}
	
	protected void paren(SVDBParenExpr expr) {
		visit(expr.getExpr());
	}

	protected void solve_before(SVDBConstraintSolveBeforeStmt expr) {
	}
	
	protected void tf_call(SVDBTFCallExpr expr) {
		if (expr.getTarget() != null) {
			visit(expr.getTarget());
		}
	}
	
	protected void unary(SVDBUnaryExpr expr) {
		visit(expr.getExpr());
	}
	
	protected void range(SVDBRangeExpr expr) {
		visit(expr.getLeft());
		visit(expr.getRight());
	}
}
