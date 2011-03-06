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

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.Stack;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVExprUtils {
	
	private static SVExprUtils			fDefault;
	private Stack<String>				fIndentStack;
	private LogHandle					fLog;
	
	public SVExprUtils() {
		fIndentStack = new Stack<String>();
		fIndentStack.push("");
		fLog = LogFactory.getLogHandle("SVExprUtils");
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
	
	protected boolean inside(PrintStream ps, SVInsideExpr expr) {
		expr_to_string(ps, expr.getLhs());
		ps.print(" inside {");
		
		for (int i=0; i<expr.getValueRangeList().size(); i++) {
			SVExpr r_i = expr.getValueRangeList().get(i);
			if (r_i.getExprType() == SVExprType.Literal) {
				literal(ps, (SVLiteralExpr)r_i);
			} else if (r_i.getExprType() == SVExprType.Range) {
				SVRangeExpr r = (SVRangeExpr)r_i;
				ps.print("[");
				expr_to_string(ps, r.getLeft());
				ps.print(":");
				expr_to_string(ps, r.getRight());
				ps.print("]");
			} else if (r_i.getExprType() == SVExprType.Identifier) {
				identifier(ps, (SVIdentifierExpr)r_i);
			}
			if (i+1 < expr.getValueRangeList().size()) {
				ps.print(", ");
			}
		}
		
		ps.print("}");
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
	
	protected boolean assign(PrintStream ps, SVAssignExpr expr) {
		expr_to_string(ps, expr.getLhs());
		ps.print(" " + expr.getOp() + " ");
		expr_to_string(ps, expr.getRhs());
		
		return true;
	}
	
	protected boolean cast(PrintStream ps, SVCastExpr expr) {
		expr_to_string(ps, expr.getCastType());
		ps.print("'(");
		expr_to_string(ps, expr.getExpr());
		ps.print(")");
		
		return true;
	}
	
	protected boolean cond(PrintStream ps, SVCondExpr expr) {
		ps.print("(");
		expr_to_string(ps, expr.getLhs());
		ps.print(")");
		ps.print("?");
		expr_to_string(ps, expr.getMhs());
		ps.print(":");
		expr_to_string(ps, expr.getRhs());
		
		return true;
	}
	
	protected boolean tf_call(PrintStream ps, SVTFCallExpr expr) {
		if (expr.getTarget() != null) {
			expr_to_string(ps, expr.getTarget());
			// TODO: may be a static reference
			ps.print(".");
		}
		ps.print(expr.getName());
		ps.print("(");
		if (expr.getArgs() != null) {
			for (int i=0; i<expr.getArgs().length; i++) {
				expr_to_string(ps, expr.getArgs()[i]);
				if (i+1 < expr.getArgs().length) {
					ps.print(", ");
				}
			}
		}
		ps.print(")");
		
		return true;
	}
	
	protected boolean field_access(PrintStream ps, SVFieldAccessExpr expr) {
		expr_to_string(ps, expr.getExpr());
		ps.print("." + expr.getId());
		return true;
	}
	
	protected boolean randomize_call(PrintStream ps, SVRandomizeCallExpr expr) {
		tf_call(ps, expr);
	
		/*
		if (expr.getWithBlock() != null) {
			ps.print(" with ");
			expr_to_string(ps, expr.getWithBlock());
		}
		 */
		
		return true;
	}

	protected boolean assignment_pattern(PrintStream ps, SVAssignmentPatternExpr expr) {
		ps.print("'{");
		for (int i=0; i<expr.getPatternList().size(); i++) {
			expr_to_string(ps, expr.getPatternList().get(i));
			if (i+1 < expr.getPatternList().size()) {
				ps.print(", ");
			}
		}
		ps.print("}");
		
		return true;
	}
	
	protected boolean incdec(PrintStream ps, SVIncDecExpr expr) {
		// TODO: need to know if this is pre- or post-dec
		expr_to_string(ps, expr.getExpr());
		ps.print(expr.getOp());
		return true;
	}
	
	protected boolean expr_to_string(PrintStream ps, SVExpr expr) {
		boolean ret = false;
		switch (expr.getExprType()) {
			case Binary: ret = binary(ps, (SVBinaryExpr)expr); break;
			case Paren: ret = paren(ps, (SVParenExpr)expr); break;
			case Identifier: ret = identifier(ps, (SVIdentifierExpr)expr); break;
			case Literal: ret = literal(ps, (SVLiteralExpr)expr); break;
			case ArrayAccess: ret = array_access(ps, (SVArrayAccessExpr)expr); break;
			case Unary: ret = unary(ps, (SVUnaryExpr)expr); break;
			case Inside: ret = inside(ps, (SVInsideExpr)expr); break;
			case Concatenation: ret = concatenation(ps, (SVConcatenationExpr)expr); break;
			case Assign: ret = assign(ps, (SVAssignExpr)expr); break;
			case Cast: ret = cast(ps, (SVCastExpr)expr); break;
			case Cond: ret = cond(ps, (SVCondExpr)expr); break;
			case TFCall: ret = tf_call(ps, (SVTFCallExpr)expr); break;
			case FieldAccess: ret = field_access(ps, (SVFieldAccessExpr)expr); break;
			case RandomizeCall: ret = randomize_call(ps, (SVRandomizeCallExpr)expr); break;
			case AssignmentPattern: ret = assignment_pattern(ps, (SVAssignmentPatternExpr)expr); break;
			case IncDec: ret = incdec(ps, (SVIncDecExpr)expr); break;
			case Null: 
				ret = true;
				ps.print("null");
				break;
			case String:
				ret = true;
				ps.print("\"" + ((SVStringExpr)expr).getContent() + "\"");
				break;
			case This:
				ret = true;
				ps.print("this");
				break;
			case Super:
				ret = true;
				ps.print("super");
				break;
			
			default:
				fLog.error("Unhandled expr in expr_to_string: " + expr.getExprType());
				break;
		}
		return ret;
	}
}
