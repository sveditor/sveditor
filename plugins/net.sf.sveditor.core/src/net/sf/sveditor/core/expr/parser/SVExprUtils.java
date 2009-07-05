package net.sf.sveditor.core.expr.parser;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;

public class SVExprUtils {
	
	public static String exprToString(SVExpr expr) {
		PrintStream ps;
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		ps = new PrintStream(bos);
		
		expr_to_string(ps, expr);
		ps.flush();
		
		return bos.toString();
	}

	public static void exprToStream(SVExpr expr, OutputStream out) {
		PrintStream ps;
		ps = new PrintStream(out);
		
		expr_to_string(ps, expr);
		ps.flush();
	}

	private static void expr_to_string(PrintStream ps, SVExpr expr) {
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
			ps.print(id.getIdStr());
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


		/*
		case Inside: {
			SVInsideExpr i_expr = (SVInsideExpr)expr;

			ps.print()
			i_expr.getLhs();

		} break;
		 */

		default:
			System.out.println("Unhandled expr in expr_to_string: " + expr.getType());
			break;
		}
	}
}
