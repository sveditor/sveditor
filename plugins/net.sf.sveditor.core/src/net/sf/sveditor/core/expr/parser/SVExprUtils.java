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


package net.sf.sveditor.core.expr.parser;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.Stack;

public class SVExprUtils {
	
	private static SVExprUtils			fDefault;
	private Stack<String>				fIndentStack;
	
	public SVExprUtils() {
		fIndentStack = new Stack<String>();
		fIndentStack.push("");
	}
	
	public void setBaseIndent(String base) {
		fIndentStack.clear();
		fIndentStack.push(base);
	}
	
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
	
	protected void push_indent() {
		fIndentStack.push(fIndentStack.peek() + "    ");
	}
	
	protected void pop_indent() {
		if (fIndentStack.size() > 1) {
			fIndentStack.pop();
		}
	}
	
	protected String get_indent() {
		return fIndentStack.peek();
	}
	
	protected boolean binary(PrintStream ps, SVBinaryExpr expr) {
		expr_to_string(ps, expr.getLhs());
		ps.print(expr.getOp());
		expr_to_string(ps, expr.getRhs());
		return true;
	}
	
	protected boolean paren(PrintStream ps, SVParenExpr expr) {
		ps.print("(");
		expr_to_string(ps, expr.getExpr());
		ps.print(")");
		return true;
	}
	
	protected boolean identifier(PrintStream ps, SVIdentifierExpr expr) {
		String id_path = getAccess(expr.getIdStr());
		ps.print(id_path);
		return true;
	}
	
	protected boolean literal(PrintStream ps, SVLiteralExpr expr) {
		SVLiteralExpr lit = (SVLiteralExpr)expr;
		ps.print(lit.getValue());
		return true;
	}
	
	protected boolean array_access(PrintStream ps, SVArrayAccessExpr expr) {
		expr_to_string(ps, expr.getLhs());

		ps.print("[");
		expr_to_string(ps, expr.getLow());
		if (expr.getHigh() != null) {
			ps.print(":");
			expr_to_string(ps, expr.getHigh());
		}
		ps.print("]");
		return true;
	}
	
	protected boolean unary(PrintStream ps, SVUnaryExpr expr) {
		ps.print(expr.getOp());
		expr_to_string(ps, expr.getExpr());
		return true;
	}
	
	protected boolean constraint_if(PrintStream ps, SVConstraintIfExpr expr) {
		SVConstraintIfExpr c_if = (SVConstraintIfExpr)expr;
		ps.print("if (");
		expr_to_string(ps, c_if.getExpr());
		ps.println(") {");
		push_indent();
		SVConstraintSetExpr if_case = (SVConstraintSetExpr)c_if.getConstraint();
		for (SVExpr c : if_case.getConstraintList()) {
			ps.print(get_indent());
			if (expr_to_string(ps, c)) {
				if (c.getType() != SVExprType.ConstraintIf) {
					ps.println(";");
				} else {
					ps.println();
				}
			} else {
				ps.println();
			}
		}
		pop_indent();
		ps.print(get_indent() + "}");
		
		if (c_if.getElseClause() != null) {
			ps.print(" else ");
			expr_to_string(ps, c_if.getElseClause());
		} else {
			ps.println();
		}
		return true;
	}
	
	protected boolean constraint_set(PrintStream ps, SVConstraintSetExpr expr) {
		ps.println("{");
		push_indent();
		for (SVExpr e : expr.getConstraintList()) {
			ps.print(get_indent());
			if (expr_to_string(ps, e)) {
				if (e.getType() != SVExprType.ConstraintIf) {
					ps.println(";");
				}
			}
		}
		pop_indent();
		ps.println(get_indent() + "} ");
		return true;
	}
	
	protected boolean inside(PrintStream ps, SVInsideExpr expr) {
		expr_to_string(ps, expr.getLhs());
		ps.print(" inside {");
		
		for (int i=0; i<expr.getValueRangeList().size(); i++) {
			SVExpr r_i = expr.getValueRangeList().get(i);
			if (r_i.getType() == SVExprType.Literal) {
				literal(ps, (SVLiteralExpr)r_i);
			} else if (r_i.getType() == SVExprType.Range) {
				SVRangeExpr r = (SVRangeExpr)r_i;
				ps.print("[");
				expr_to_string(ps, r.getLeft());
				ps.print(":");
				expr_to_string(ps, r.getRight());
				ps.print("]");
			} else if (r_i.getType() == SVExprType.Identifier) {
				identifier(ps, (SVIdentifierExpr)r_i);
			}
			if (i+1 < expr.getValueRangeList().size()) {
				ps.print(", ");
			}
		}
		
		ps.print("}");
		return true;
	}
	
	protected boolean implication(PrintStream ps, SVImplicationExpr expr) {
		expr_to_string(ps, expr.getExpr());
		
		ps.print(" -> ");
		
		expr_to_string(ps, expr.getConstraintSet());
		return true;
	}
	
	protected boolean concatenation(PrintStream ps, SVConcatenationExpr expr) {
		ps.print("{");
		
		for (int i=0; i<expr.getElements().size(); i++) {
			expr_to_string(ps, expr.getElements().get(i));
			if (i+1 < expr.getElements().size()) {
				ps.print(", ");
			}
		}
		
		ps.print("}");
		return true;
	}
	
	protected boolean dist_list(PrintStream ps, SVDistListExpr expr) {
		expr_to_string(ps, expr.getLHS());
		ps.print(" dist {");
		for (int i=0; i<expr.getDistItems().size(); i++) {
			SVDistItemExpr item = expr.getDistItems().get(i);
			expr_to_string(ps, item.getLHS());
			ps.print(" " + (item.isDist()?":/":":=") + " ");
			expr_to_string(ps, item.getRHS());
		}
		ps.print("}");
		
		return true;
	}
	
	protected boolean expr_to_string(PrintStream ps, SVExpr expr) {
		boolean ret = false;
		switch (expr.getType()) {
			case Binary: ret = binary(ps, (SVBinaryExpr)expr); break;
			case Paren: ret = paren(ps, (SVParenExpr)expr); break;
			case Identifier: ret = identifier(ps, (SVIdentifierExpr)expr); break;
			case Literal: ret = literal(ps, (SVLiteralExpr)expr); break;
			case ArrayAccess: ret = array_access(ps, (SVArrayAccessExpr)expr); break;
			case Unary: ret = unary(ps, (SVUnaryExpr)expr); break;
			case ConstraintIf: ret = constraint_if(ps, (SVConstraintIfExpr)expr); break;
			case ConstraintSet: ret = constraint_set(ps, (SVConstraintSetExpr)expr); break;
			case Inside: ret = inside(ps, (SVInsideExpr)expr); break;
			case Implication: ret = implication(ps, (SVImplicationExpr)expr); break;
			case Concatenation: ret = concatenation(ps, (SVConcatenationExpr)expr); break;
			case DistList: ret = dist_list(ps, (SVDistListExpr)expr); break;
			default:
				System.out.println("[ERROR] Unhandled expr in expr_to_string: " + expr.getType());
				break;
		}
		return ret;
	}
}
