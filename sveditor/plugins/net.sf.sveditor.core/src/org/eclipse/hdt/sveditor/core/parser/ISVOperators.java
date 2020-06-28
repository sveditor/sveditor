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
package org.eclipse.hdt.sveditor.core.parser;

public interface ISVOperators {
	
	enum OP {
		AND("&"),
		AND2("&&"),
		AND3("&&&"),
		OR("|"),
		OR2("||"),
		MINUS("-"),
		PLUS("+"),
		MOD("%"),
		NOT("!"),
		MUL("*"),
		DOLLAR("$"),
		MUL2("**"),
		DIV("/"),
		XOR("^"),
		XOR_NEG("^~"),
		NEG_XOR("~^"),
		NEG("~"),
		NEG_AND("~&"),
		NEG_OR("~|"),
		TERNARY("?"),
		LT("<"),
		LT_PLUS("<+"),
		LSHIFT("<<"),
		LE("<="),
		LSHIFT3("<<<"),
		GT(">"),
		RSHIFT(">>"),
		GE(">="),
		EQ_GT("=>"),
		RSHIFT3(">>>"),
		EQ("="),
		MUL_EQ("*="),
		DIV_EQ("/="),
		MOD_EQ("%="),
		PLUS_EQ("+="),
		EQ2("=="),
		NOT_EQ("!="),
		SUB_EQ("-="),
		LSHIFT_EQ("<<="),
		RSHIFT_EQ(">>="),
		LSHIFT3_EQ("<<<="),
		RSHIFT3_EQ(">>>="),
		AND_EQ("&="),
		XOR_EQ("^="),
		OR_EQ("|="),
		EQ3("==="),
		NOT_EQ2("!=="),
		EQ2_TERN("==?"),
		NOT_EQ_TERN("!=?"),
		LPAREN("("),
		RPAREN(")"),
		LBRACE("{"),
		RBRACE("}"),
		LBRACKET("["),
		RBRACKET("]"),
		
		COLON(":"),
		COLON2("::"),
		COLON_DIV(":/"),
		COLON_EQ(":="),
		PLUS_COLON("+:"),
		SUB_COLON("-:"),
		COMMA(","),
		SEMICOLON(";"),
		DOT("."),
		DOT_MUL(".*"),
		SQUOTE("'"),
		IMPL("->"),
		IMPL_BIDIR("<->"),
		IMPL_RSHIFT("->>"),
		IMPL2("-->"),
		HASH("#"),
		HASH2("##"),
		AT("@"),
		AT2("@@"),
		LPAREN_MUL("(*"),
		MUL_RPAREN("*)"),
		OR_EQ_GT("|=>"),
		OR_IMPL("|->"),
		HASH_SUB_HASH("#-#"),
		HASH_EQ_HASH("#=#"),
		PLUS_GE("+=>"),
		SUB_GE("-=>"),
		MUL_GT("*>"),
		SUB_MUL_GT("-*>"),
		PLUS_MUL_GT("+*>"),
		DEC("--"),
		INC("++")
		;
		
		
		String		fImg;
		
		public String getImg() { return fImg; }
		
		OP(String img) {
			fImg = img;
		}
	}

}
