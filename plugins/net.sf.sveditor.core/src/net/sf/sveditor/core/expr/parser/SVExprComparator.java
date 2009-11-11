package net.sf.sveditor.core.expr.parser;

public class SVExprComparator {
	
	public boolean equal(SVExpr a, SVExpr b) {
		return equal_int(a, b);
	}
	
	private boolean equal_int(SVExpr a, SVExpr b) {
		boolean equal = true;
		
		if (a.getType() == SVExprType.Paren) {
			return equal_int(((SVParenExpr)a).getExpr(), b);
		}
		
		if (b.getType() == SVExprType.Paren) {
			return equal_int(a, ((SVParenExpr)b).getExpr());
		}
		
		if (a.getType() != b.getType()) {
			return false;
		}
		
		switch (a.getType()) {
			case ArrayAccess: {
				SVArrayAccessExpr aa_a = (SVArrayAccessExpr)a;
				SVArrayAccessExpr aa_b = (SVArrayAccessExpr)b;
				
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
				
			case Assign: {
				SVAssignExpr ae_a = (SVAssignExpr)a;
				SVAssignExpr ae_b = (SVAssignExpr)b;
				
				equal &= ae_a.getOp().equals(ae_b.getOp());
				
				equal &= equal_int(ae_a.getLhs(), ae_b.getLhs());
				equal &= equal_int(ae_a.getRhs(), ae_b.getRhs());
			} break;
				
			case Binary: {
				SVBinaryExpr be_a = (SVBinaryExpr)a;
				SVBinaryExpr be_b = (SVBinaryExpr)b;
				
				equal &= be_a.getOp().equals(be_b.getOp());
				
				equal &= equal_int(be_a.getLhs(), be_b.getLhs());
				
				equal &= equal_int(be_a.getRhs(), be_b.getRhs());
			} break;
			
			case Identifier: {
				SVIdentifierExpr id_a = (SVIdentifierExpr)a;
				SVIdentifierExpr id_b = (SVIdentifierExpr)b;
				
				equal &= id_a.getIdStr().equals(id_b.getIdStr());
			} break;
			
			case Unary: {
				SVUnaryExpr un_a = (SVUnaryExpr)a;
				SVUnaryExpr un_b = (SVUnaryExpr)b;
				
				equal &= (un_a.getOp().equals(un_b.getOp()));
				equal &= (equal_int(un_a.getExpr(), un_b.getExpr()));
			} break;
			
			case Literal: {
				SVLiteralExpr lit_a = (SVLiteralExpr)a;
				SVLiteralExpr lit_b = (SVLiteralExpr)b;
				
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
