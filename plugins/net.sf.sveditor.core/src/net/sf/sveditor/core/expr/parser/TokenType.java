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

public enum TokenType {
	Id,
	Keyword,
	
	LeftBrace,		// {
	RightBrace,		// }
	LeftBracket,	// [
	RightBracket,	// ]
	LeftParen,		// (
	RightParen,		// )
	Comma,			// ,
	
	
	Implication,	// ->
	ColonEquals,	// :=
	ColonDiv,		// :/
	
	LT,				// <
	GT,				// >
	GE,				// >=
	LE,				// <=
	Plus,			// +
	PlusPlus,		// ++
	Minus,			// -
	MinusMinus,		// --
	BitAnd,			// &
	BoolAnd,		// &&
	BitOr,			// |
	BoolOr,			// ||
	Number,
	EOF

}
