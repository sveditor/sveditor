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
	
	public void dump(SVExpr expr) {
		dump_i(expr);
		
		fPS.flush();
	}
	
	public String toString(SVExpr expr) {
		ByteOutputStream bos = new ByteOutputStream();
		PrintStream tmp = fPS;
		fPS = new PrintStream(bos);
		dump_i(expr);
		fPS.flush();
		fPS = tmp;
		return bos.toString();
	}
	
	private void dump_i(SVExpr expr) {
		switch (expr.getExprType()) {
			case ArrayAccess: {
				
			} break;
			
			case Assign: {
				
			} break;
			
			case Binary: {
				SVBinaryExpr bin = (SVBinaryExpr)expr;
				dump_i(bin.getLhs());
				fPS.print(" " + bin.getOp() + " ");
				dump_i(bin.getRhs());
			} break;
			
			case Cast: {
				
			} break;
			
			case Cond: {
				
			} break;
			
			case FieldAccess: {
				
			} break;
			
			case Identifier: {
				SVIdentifierExpr id = (SVIdentifierExpr)expr;
				StringBuilder id_s = new StringBuilder();
				
				for (int i=0; i<id.getId().length; i++) {
					id_s.append(id.getId()[i]);
					if (i+1 < id.getId().length) {
						id_s.append(".");
					}
				}
				
				fPS.print(id_s.toString());
			} break;
			
			case IncDec: {
				SVIncDecExpr incdec = (SVIncDecExpr)expr;
				dump_i(incdec.getExpr());
				fPS.print(incdec.getOp());
			} break;
		
			case Literal: {
				SVLiteralExpr lit = (SVLiteralExpr)expr;
				fPS.print(lit.getValue());
			} break;
			
			case Paren: {
				SVParenExpr p = (SVParenExpr)expr;
				
				fPS.print("(");
				dump_i(p.getExpr());
				fPS.print(")");
			} break;
			
			case QualifiedSuperFieldRef: {
				
			} break;
			
			case QualifiedThisRef: {
			} break;
		
			case TFCall: {
				
			} break;
			
			case Unary: {
				SVUnaryExpr u = (SVUnaryExpr)expr;
				
				fPS.print(u.getOp());
				dump_i(u.getExpr());
			} break;
			
		}
	}

}
