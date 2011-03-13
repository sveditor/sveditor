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

import java.io.PrintStream;

import com.sun.xml.internal.messaging.saaj.util.ByteOutputStream;

public class SVExprDump {
	
	private PrintStream			fPS;
	
	public SVExprDump(PrintStream ps) {
		fPS = ps;
	}
	
	public void dump(SVDBExpr expr) {
		dump_i(expr);
		
		fPS.flush();
	}
	
	public String toString(SVDBExpr expr) {
		ByteOutputStream bos = new ByteOutputStream();
		PrintStream tmp = fPS;
		fPS = new PrintStream(bos);
		dump_i(expr);
		fPS.flush();
		fPS = tmp;
		return bos.toString();
	}
	
	private void dump_i(SVDBExpr expr) {
		switch (expr.getType()) {
			case ArrayAccessExpr: {
				
			} break;
			
			case AssignExpr: {
				
			} break;
			
			case BinaryExpr: {
				SVDBBinaryExpr bin = (SVDBBinaryExpr)expr;
				dump_i(bin.getLhs());
				fPS.print(" " + bin.getOp() + " ");
				dump_i(bin.getRhs());
			} break;
			
			case CastExpr: {
				
			} break;
			
			case CondExpr: {
				
			} break;
			
			case FieldAccessExpr: {
				
			} break;
			
			case IdentifierExpr: {
				SVDBIdentifierExpr id = (SVDBIdentifierExpr)expr;
				StringBuilder id_s = new StringBuilder();
				
				for (int i=0; i<id.getId().size(); i++) {
					id_s.append(id.getId().get(i));
					if (i+1 < id.getId().size()) {
						id_s.append(".");
					}
				}
				
				fPS.print(id_s.toString());
			} break;
			
			case IncDecExpr: {
				SVDBIncDecExpr incdec = (SVDBIncDecExpr)expr;
				dump_i(incdec.getExpr());
				fPS.print(incdec.getOp());
			} break;
		
			case LiteralExpr: {
				SVDBLiteralExpr lit = (SVDBLiteralExpr)expr;
				fPS.print(lit.getValue());
			} break;
			
			case ParenExpr: {
				SVDBParenExpr p = (SVDBParenExpr)expr;
				
				fPS.print("(");
				dump_i(p.getExpr());
				fPS.print(")");
			} break;
			
			case QualifiedSuperFieldRefExpr: {
				
			} break;
			
			case QualifiedThisRefExpr: {
			} break;
		
			case TFCallExpr: {
				
			} break;
			
			case UnaryExpr: {
				SVDBUnaryExpr u = (SVDBUnaryExpr)expr;
				
				fPS.print(u.getOp());
				dump_i(u.getExpr());
			} break;
			
		}
	}

}
