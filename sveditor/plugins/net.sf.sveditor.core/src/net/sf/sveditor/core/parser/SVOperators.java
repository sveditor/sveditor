/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.parser;

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.parser.ISVOperators.OP;

public class SVOperators {

	public static final OP RelationalOps[] = { 
		OP.AND, OP.AND2, OP.AND3, OP.OR, OP.OR2, OP.MINUS,
		OP.PLUS, OP.MOD, OP.NOT, OP.MUL, OP.MUL2, OP.DIV, OP.XOR, OP.XOR_NEG, OP.NEG_XOR, OP.NEG,
		OP.TERNARY, OP.COLON, OP.LT, OP.LSHIFT, OP.LE, OP.LSHIFT3, OP.GT, OP.RSHIFT, OP.GE, OP.RSHIFT3, OP.EQ, OP.MUL_EQ,
		OP.DIV_EQ, OP.MOD_EQ, OP.PLUS_EQ, OP.EQ2, OP.NOT_EQ, OP.SUB_EQ, OP.LSHIFT_EQ, OP.RSHIFT_EQ, OP.LSHIFT3_EQ, OP.RSHIFT3_EQ,
		OP.AND_EQ, OP.XOR_EQ, OP.OR_EQ, OP.EQ3, OP.NOT_EQ2, OP.EQ2_TERN, OP.NOT_EQ_TERN};
	
	public static final Set<OP> RelationalOpsE;
	static {
		RelationalOpsE = new HashSet<ISVOperators.OP>();
		for (OP op : RelationalOps) {
			RelationalOpsE.add(op);
		}
	}
	
	public static final String ComparisonAssignOps[] = { 
		"<", "<=", ">", ">=", "=", "*=",
		"/=", "%=", "+=", "==", "!=", "-=", "<<=", ">>=", "<<<=", ">>>=",
		"&=", "^=", "|=", "===", "!==", "==?", "!=?"};

	public static final String GroupingOps[] = { "(", ")", "{", "}", "[", "]", };

	public static final String MiscOps[] = { ":", "::", ":/", ":=", "+:", "-:", // array-index
		// operators
		",", ";", ".", ".*", "'", "->", "->>", "-->", "#", "##", "@", "@@", "(*", "*)",
		// Assertion operators
		"=>", "|=>", "|->", "#-#", "#=#", 
		// Specify Operators
		/*"=>", already included*/ "+=>", "-=>", "*>", "-*>", "+*>",
		"--", "++"};

	public static final String AllOperators[];

	static {
//		AllOperators = new String[RelationalOps.length + GroupingOps.length
//		                          + MiscOps.length];
		AllOperators = new String[OP.values().length];
		
		int idx = 0;
		for (OP op : OP.values()) {
			AllOperators[idx++] = op.getImg();
		}
	}
	
	public static final Set<OP>					fAssignmentOps;

	static {
		fAssignmentOps = new HashSet<OP>();
		fAssignmentOps.add(OP.EQ);
		fAssignmentOps.add(OP.PLUS_EQ);
		fAssignmentOps.add(OP.SUB_EQ);
		fAssignmentOps.add(OP.MUL_EQ);
		fAssignmentOps.add(OP.DIV_EQ);
		fAssignmentOps.add(OP.AND_EQ);
		fAssignmentOps.add(OP.OR_EQ);
		fAssignmentOps.add(OP.XOR_EQ);
		fAssignmentOps.add(OP.MOD_EQ);
		fAssignmentOps.add(OP.LSHIFT_EQ);
		fAssignmentOps.add(OP.RSHIFT_EQ);
		fAssignmentOps.add(OP.LSHIFT3_EQ);
		fAssignmentOps.add(OP.RSHIFT3_EQ);
		fAssignmentOps.add(OP.LE);
		fAssignmentOps.add(OP.LT_PLUS);
//		fAssignmentOps.add("->");				// force an event		
	}
	
	public static final Set<OP>					fBinaryOps;
	
	static {
		fBinaryOps = new HashSet<OP>();
		for (OP op : new OP[] {OP.AND, OP.AND2, OP.OR, OP.OR2, OP.MINUS,
				OP.PLUS, OP.MOD, OP.NOT, OP.MUL, OP.MUL2, OP.DIV, OP.XOR, OP.XOR_NEG, OP.NEG_XOR, OP.NEG,
				OP.TERNARY, OP.LT, OP.LSHIFT, OP.LE, OP.LSHIFT3, OP.GT, OP.RSHIFT, OP.GE, OP.RSHIFT3, OP.EQ, OP.MUL_EQ,
				OP.DIV_EQ, OP.MOD_EQ, OP.PLUS_EQ, OP.EQ2, OP.NOT_EQ, OP.SUB_EQ, OP.LSHIFT_EQ, OP.RSHIFT_EQ, OP.LSHIFT3_EQ, OP.RSHIFT3_EQ,
				OP.AND_EQ, OP.XOR_EQ, OP.OR_EQ, OP.EQ3, OP.NOT_EQ2, OP.EQ2_TERN, OP.DEC, OP.INC, OP.NEG_AND, OP.NEG_OR, OP.COLON}) {
			fBinaryOps.add(op);
		}
	}
}
