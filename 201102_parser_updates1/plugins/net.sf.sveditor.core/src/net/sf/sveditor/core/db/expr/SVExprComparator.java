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

import net.sf.sveditor.core.db.SVDBItemType;

public class SVExprComparator {
	
	public boolean equal(SVDBExpr a, SVDBExpr b) {
		return equal_int(a, b);
	}
	
	private boolean equal_int(SVDBExpr a, SVDBExpr b) {
		boolean equal = true;
		
		if (a.getType() == SVDBItemType.ParenExpr) {
			return equal_int(((SVDBParenExpr)a).getExpr(), b);
		}
		
		if (b.getType() == SVDBItemType.ParenExpr) {
			return equal_int(a, ((SVDBParenExpr)b).getExpr());
		}
		
		if (a.getType() != b.getType()) {
			return false;
		}
		
		switch (a.getType()) {
			case ArrayAccessExpr: {
				SVDBArrayAccessExpr aa_a = (SVDBArrayAccessExpr)a;
				SVDBArrayAccessExpr aa_b = (SVDBArrayAccessExpr)b;
				
				equal &= (aa_a.getLow() == null || aa_b.getLow() == null &&
						aa_a.getLow() != aa_b.getLow());
				
				equal &= (aa_a.getHigh() == null || aa_b.getHigh() == null &&
						aa_a.getHigh() != aa_b.getHigh());
				
				if (aa_a.getLow() != null && aa_b.getLow() != null) {
					equal &= equal_int(aa_a.getLow(), aa_b.getLow());
				}

				if (aa_a.getHigh() != null && aa_b.getHigh() != null) {
					equal &= equal_int(aa_a.getHigh(), aa_b.getHigh());
				}

				equal &= equal_int(aa_a.getLhs(), aa_b.getLhs());
			} break;
				
			case AssignExpr: {
				SVDBAssignExpr ae_a = (SVDBAssignExpr)a;
				SVDBAssignExpr ae_b = (SVDBAssignExpr)b;
				
				equal &= ae_a.getOp().equals(ae_b.getOp());
				
				equal &= equal_int(ae_a.getLhs(), ae_b.getLhs());
				equal &= equal_int(ae_a.getRhs(), ae_b.getRhs());
			} break;
				
			case BinaryExpr: {
				SVDBBinaryExpr be_a = (SVDBBinaryExpr)a;
				SVDBBinaryExpr be_b = (SVDBBinaryExpr)b;
				
				equal &= be_a.getOp().equals(be_b.getOp());
				
				equal &= equal_int(be_a.getLhs(), be_b.getLhs());
				
				equal &= equal_int(be_a.getRhs(), be_b.getRhs());
			} break;
			
			case IdentifierExpr: {
				SVDBIdentifierExpr id_a = (SVDBIdentifierExpr)a;
				SVDBIdentifierExpr id_b = (SVDBIdentifierExpr)b;
				
				equal &= id_a.getIdStr().equals(id_b.getIdStr());
			} break;
			
			case UnaryExpr: {
				SVDBUnaryExpr un_a = (SVDBUnaryExpr)a;
				SVDBUnaryExpr un_b = (SVDBUnaryExpr)b;
				
				equal &= (un_a.getOp().equals(un_b.getOp()));
				equal &= (equal_int(un_a.getExpr(), un_b.getExpr()));
			} break;
			
			case LiteralExpr: {
				SVDBLiteralExpr lit_a = (SVDBLiteralExpr)a;
				SVDBLiteralExpr lit_b = (SVDBLiteralExpr)b;
				
				equal &= (lit_a.getValue().equals(lit_b.getValue()));
			} break;
				
			
			default:
				System.out.println("[ERROR] expression type \"" + a.getType() + "\" not handled in comparison");
				equal = false;
				break;
		}
		
		return equal;
	}

}
