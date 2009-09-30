package net.sf.sveditor.core.expr.parser;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;

public class SVExprUtils {
	
	private static SVExprUtils			fDefault;
	
	public static SVExprUtils getDefault() {
		if (fDefault == null) {
			fDefault = new SVExprUtils();
		}
		return fDefault;
	}
	
	public String exprToString(SVExpr expr) {
		PrintStream ps;
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		ps = new PrintStream(bos);
		
		expr_to_string(ps, expr);
		ps.flush();
		
		return bos.toString();
	}

	public void exprToStream(SVExpr expr, OutputStream out) {
		PrintStream ps;
		ps = new PrintStream(out);
		
		expr_to_string(ps, expr);
		ps.flush();
	}
	
	protected String getAccess(String id) {
		return id;
	}

	private void expr_to_string(PrintStream ps, SVExpr expr) {
		switch (expr.getType()) {
		case Binary: {
			SVBinaryExpr bin_expr = (SVBinaryExpr)expr;
			expr_to_string(ps, bin_expr.getLhs());
			ps.print(bin_expr.getOp());
			expr_to_string(ps, bin_expr.getRhs());
		} break;

		case Paren: {
			SVParenExpr p_expr = (SVParenExpr)expr;
			ps.print("(");
			expr_to_string(ps, p_expr.getExpr());
			ps.print(")");
		} break;

		case Identifier: {
			SVIdentifierExpr id = (SVIdentifierExpr)expr;
			
			String id_path = getAccess(id.getIdStr());
			ps.print(id_path);
		} break;

		case Literal: {
			SVLiteralExpr lit = (SVLiteralExpr)expr;
			ps.print(lit.getValue());
		} break;

		case ArrayAccess: {
			SVArrayAccessExpr a_expr = (SVArrayAccessExpr)expr;

			expr_to_string(ps, a_expr.getLhs());

			ps.print("[");
			expr_to_string(ps, a_expr.getLow());
			if (a_expr.getHigh() != null) {
				ps.print(":");
				expr_to_string(ps, a_expr.getHigh());
			}
			ps.print("]");
		} break;

		case Unary: {
			SVUnaryExpr u_expr = (SVUnaryExpr)expr;

			ps.print(u_expr.getOp());
			expr_to_string(ps, u_expr.getExpr());
		} break;
		
		case ConstraintIf: {
			SVConstraintIfExpr c_if = (SVConstraintIfExpr)expr;
			ps.print("if (");
			expr_to_string(ps, c_if.getExpr());
			ps.print(") ");
			expr_to_string(ps, c_if.getConstraint());
			
			if (c_if.getElseClause() != null) {
				ps.print("else ");
				expr_to_string(ps, c_if.getElseClause());
			}
		} break;
		
		case ConstraintSet: {
			SVConstraintSetExpr c_set = (SVConstraintSetExpr)expr;

			ps.print("{ ");
			for (SVExpr e : c_set.getConstraintList()) {
				expr_to_string(ps, e);
				ps.print("; ");
			}
			ps.print("} ");
			} break;

		case Inside: {
			SVInsideExpr i_expr = (SVInsideExpr)expr;

			expr_to_string(ps, i_expr.getLhs());
			ps.print(" inside {");
			
			for (int i=0; i<i_expr.getValueRangeList().size(); i++) {
				SVExpr r_i = i_expr.getValueRangeList().get(i);
				if (r_i.getType() == SVExprType.Literal) {
					ps.print(((SVLiteralExpr)r_i).getValue());
				} else if (r_i.getType() == SVExprType.Range) {
					SVRangeExpr r = (SVRangeExpr)r_i;
					ps.print("[");
					expr_to_string(ps, r.getLeft());
					ps.print(":");
					expr_to_string(ps, r.getRight());
					ps.print("]");
				} else if (r_i.getType() == SVExprType.Identifier) {
					ps.print(getAccess(((SVIdentifierExpr)r_i).getIdStr()));
				}
				if (i+1 < i_expr.getValueRangeList().size()) {
					ps.print(", ");
				}
			}
			
			ps.print("}");
		} break;
		
		case Implication: {
			SVImplicationExpr impl = (SVImplicationExpr)expr;
			
			expr_to_string(ps, impl.getExpr());
			
			ps.print(" -> ");
			
			expr_to_string(ps, impl.getConstraintSet());
			
		} break;
		
		case Concatenation: {
			SVConcatenationExpr concat = (SVConcatenationExpr)expr;
			
			ps.print("{");
			
			for (int i=0; i<concat.getElements().size(); i++) {
				expr_to_string(ps, concat.getElements().get(i));
				if (i+1 < concat.getElements().size()) {
					ps.print(", ");
				}
			}
			
			ps.print("}");
			
		} break;

		default:
			System.out.println("[ERROR] Unhandled expr in expr_to_string: " + expr.getType());
			break;
		}
	}
}
