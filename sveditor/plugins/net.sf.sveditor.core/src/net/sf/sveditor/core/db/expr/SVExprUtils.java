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

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.Stack;

import net.sf.sveditor.core.db.SVDBItemType;
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
	
	public String exprToString(SVDBExpr expr) {
		PrintStream ps;
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		ps = new PrintStream(bos);
		
		expr_to_string(ps, expr);
		ps.flush();
		
		return bos.toString();
	}

	public void exprToStream(SVDBExpr expr, OutputStream out) {
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
	
	protected boolean binary(PrintStream ps, SVDBBinaryExpr expr) {
		expr_to_string(ps, expr.getLhs());
		ps.print(expr.getOp());
		expr_to_string(ps, expr.getRhs());
		return true;
	}
	
	protected boolean paren(PrintStream ps, SVDBParenExpr expr) {
		ps.print("(");
		expr_to_string(ps, expr.getExpr());
		ps.print(")");
		return true;
	}
	
	protected boolean range(PrintStream ps, SVDBRangeExpr expr) {
		expr_to_string(ps, expr.getLeft());
		ps.print(":");
		expr_to_string(ps, expr.getRight());
		return true;
	}
	
	protected boolean identifier(PrintStream ps, SVDBIdentifierExpr expr) {
		String id_path = getAccess(expr.getId());
		ps.print(id_path);
		return true;
	}
	
	protected boolean literal(PrintStream ps, SVDBLiteralExpr expr) {
		SVDBLiteralExpr lit = (SVDBLiteralExpr)expr;
		ps.print(lit.getValue());
		return true;
	}
	
	protected boolean array_access(PrintStream ps, SVDBArrayAccessExpr expr) {
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
	
	protected boolean unary(PrintStream ps, SVDBUnaryExpr expr) {
		ps.print(expr.getOp());
		expr_to_string(ps, expr.getExpr());
		return true;
	}
	
	protected boolean inside(PrintStream ps, SVDBInsideExpr expr) {
		expr_to_string(ps, expr.getLhs());
		ps.print(" inside {");
		
		for (int i=0; i<expr.getValueRangeList().size(); i++) {
			SVDBExpr r_i = expr.getValueRangeList().get(i);
			if (r_i.getType() == SVDBItemType.LiteralExpr) {
				literal(ps, (SVDBLiteralExpr)r_i);
			} else if (r_i.getType() == SVDBItemType.RangeExpr) {
				SVDBRangeExpr r = (SVDBRangeExpr)r_i;
				ps.print("[");
				expr_to_string(ps, r.getLeft());
				ps.print(":");
				expr_to_string(ps, r.getRight());
				ps.print("]");
			} else if (r_i.getType() == SVDBItemType.IdentifierExpr) {
				identifier(ps, (SVDBIdentifierExpr)r_i);
			}
			if (i+1 < expr.getValueRangeList().size()) {
				ps.print(", ");
			}
		}
		
		ps.print("}");
		return true;
	}
	
	protected boolean concatenation(PrintStream ps, SVDBConcatenationExpr expr) {
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
	
	protected boolean assign(PrintStream ps, SVDBAssignExpr expr) {
		expr_to_string(ps, expr.getLhs());
		ps.print(" " + expr.getOp() + " ");
		expr_to_string(ps, expr.getRhs());
		
		return true;
	}
	
	protected boolean cast(PrintStream ps, SVDBCastExpr expr) {
		expr_to_string(ps, expr.getCastType());
		ps.print("'(");
		expr_to_string(ps, expr.getExpr());
		ps.print(")");
		
		return true;
	}
	
	protected boolean cond(PrintStream ps, SVDBCondExpr expr) {
		ps.print("(");
		expr_to_string(ps, expr.getLhs());
		ps.print(")");
		ps.print("?");
		expr_to_string(ps, expr.getMhs());
		ps.print(":");
		expr_to_string(ps, expr.getRhs());
		
		return true;
	}
	
	protected boolean tf_call(PrintStream ps, SVDBTFCallExpr expr) {
		if (expr.getTarget() != null) {
			expr_to_string(ps, expr.getTarget());
			// TODO: may be a static reference
			ps.print(".");
		}
		ps.print(expr.getName());
		ps.print("(");
		if (expr.getArgs() != null) {
			for (int i=0; i<expr.getArgs().size(); i++) {
				expr_to_string(ps, expr.getArgs().get(i));
				if (i+1 < expr.getArgs().size()) {
					ps.print(", ");
				}
			}
		}
		ps.print(")");
		
		return true;
	}
	
	protected boolean field_access(PrintStream ps, SVDBFieldAccessExpr expr) {
		expr_to_string(ps, expr.getExpr());
		ps.print(".");
		expr_to_string(ps, expr.getLeaf());
		return true;
	}
	
	protected boolean randomize_call(PrintStream ps, SVDBRandomizeCallExpr expr) {
		tf_call(ps, expr);
	
		/*
		if (expr.getWithBlock() != null) {
			ps.print(" with ");
			expr_to_string(ps, expr.getWithBlock());
		}
		 */
		
		return true;
	}

	protected boolean assignment_pattern(PrintStream ps, SVDBAssignmentPatternExpr expr) {
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
	
	protected boolean incdec(PrintStream ps, SVDBIncDecExpr expr) {
		// TODO: need to know if this is pre- or post-dec
		expr_to_string(ps, expr.getExpr());
		ps.print(expr.getOp());
		return true;
	}
	
	protected boolean expr_to_string(PrintStream ps, SVDBExpr expr) {
		boolean ret = false;
		
		if (expr == null) {
			return ret;
		}
		
		switch (expr.getType()) {
			case ArrayAccessExpr: ret = array_access(ps, (SVDBArrayAccessExpr)expr); break;
			case AssignExpr: ret = assign(ps, (SVDBAssignExpr)expr); break;
			case AssignmentPatternExpr: ret = assignment_pattern(ps, (SVDBAssignmentPatternExpr)expr); break;
			case AssignmentPatternRepeatExpr: 
				// TODO:
				break;
			case AssociativeArrayElemAssignExpr:
				// TODO:
				break;
			case BinaryExpr: ret = binary(ps, (SVDBBinaryExpr)expr); break;
			case CastExpr: ret = cast(ps, (SVDBCastExpr)expr); break;
			case ClockingEventExpr:
				// TODO:
				break;
			case ConcatenationExpr: ret = concatenation(ps, (SVDBConcatenationExpr)expr); break;
			case CondExpr: ret = cond(ps, (SVDBCondExpr)expr); break;
			// TODO: CrossBinsSelectConditionExpr
			// TODO: CtorExpr
			// TODO: CycleDelayExpr
			case FieldAccessExpr: ret = field_access(ps, (SVDBFieldAccessExpr)expr); break;
			// TODO: FirstMatchExpr
			case IdentifierExpr: ret = identifier(ps, (SVDBIdentifierExpr)expr); break;
			case IncDecExpr: ret = incdec(ps, (SVDBIncDecExpr)expr); break;
			case InsideExpr: ret = inside(ps, (SVDBInsideExpr)expr); break;
			case LiteralExpr: ret = literal(ps, (SVDBLiteralExpr)expr); break;
			// TODO: MinTypMaxExpr
			// TODO: NamedArgExpr
			case NameMappedExpr:
			// TODO: NameMappedExpr
				break;
			case NullExpr: 
				ret = true;
				ps.print("null");
				break;
			// TODO: ParamIdExpr
			case ParenExpr: ret = paren(ps, (SVDBParenExpr)expr); break;
			// TODO: PropertyWeakStrongExpr
			case RandomizeCallExpr: ret = randomize_call(ps, (SVDBRandomizeCallExpr)expr); break;
			// TODO: RangeDollarBoundExpr
			case RangeExpr: ret = range(ps, (SVDBRangeExpr)expr); break;
			case TFCallExpr: ret = tf_call(ps, (SVDBTFCallExpr)expr); break;
			case UnaryExpr: ret = unary(ps, (SVDBUnaryExpr)expr); break;
			case TypeExpr: {
				SVDBTypeExpr type = (SVDBTypeExpr)expr;
				ps.print("Type: " + type.getTypeInfo());
			} break;
			case StringExpr:
				ret = true;
				ps.print("\"" + ((SVDBStringExpr)expr).getContent() + "\"");
				break;
				
			default:
				try {
					throw new Exception();
				} catch (Exception e) {
					fLog.debug("Unhandled expr in expr_to_string: " + expr.getType(), e);
				}
				break;
		}
		return ret;
	}
}
