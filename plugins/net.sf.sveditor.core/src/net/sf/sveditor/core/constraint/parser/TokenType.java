package net.sf.sveditor.core.constraint.parser;

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
