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


package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;

public class SVBehavioralBlockParser extends SVParserBase {
	private static SVDBItem				fSpecialNonNull;
	static {
		fSpecialNonNull = new SVDBItem("BehavioralSpecialNonNull", SVDBItemType.VarDecl);
		fSpecialNonNull.setLocation(new SVDBLocation(-1));
	}
	
	public SVBehavioralBlockParser(ISVParser parser) {
		super(parser);
	}
	
	
	public SVDBItem parse() throws SVParseException {
		SVDBItem ret = null;
		statement("", 0);
		return ret;
	}
	
	private void statement(String parent, int level) throws SVParseException {
		debug("--> [" + level + "] parent=" + parent + " statement " + 
				lexer().peek() + " @ " + lexer().getStartLocation().getLine());
		if (lexer().peekKeyword("begin")) {
			lexer().eatToken();
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				lexer().readId();
			}
			while (lexer().peek() != null && !lexer().peekKeyword("end")) {
				statement(parent, level+1);
			}
			lexer().readKeyword("end");
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				lexer().readId();
			}
		} else if (lexer().peekKeyword("if")) {
			lexer().eatToken();
			
			lexer().readOperator("(");
			parsers().SVParser().readExpression();
			lexer().readOperator(")");
			
			statement("if", level);
			
			if (lexer().peekKeyword("else")) {
				lexer().eatToken();
				statement("else", level);
			}
		} else if (lexer().peekKeyword("else")) {
			lexer().eatToken();
			statement("else", level);
		} else if (lexer().peekKeyword("while")) {
			lexer().eatToken();
			lexer().readOperator("(");
			parsers().SVParser().readExpression();
			lexer().readOperator(")");
			
			statement("while", level);
		} else if (lexer().peekKeyword("do")) {
			lexer().eatToken();
			statement("do", level);
			lexer().readKeyword("while");
			lexer().readOperator("(");
			String expr = parsers().SVParser().readExpression();
			debug("While expression: " + expr);
			lexer().readOperator(")");
			lexer().readOperator(";");
		} else if (lexer().peekKeyword("repeat")) {
			lexer().eatToken();
			lexer().readOperator("(");
			parsers().SVParser().readExpression(false);
			lexer().readOperator(")");
			statement("repeat", level);
		} else if (lexer().peekKeyword("forever")) {
			lexer().eatToken();
			statement("forever", level);
		} else if (lexer().peekKeyword("for")) {
			lexer().eatToken();
			lexer().readOperator("(");
			lexer().skipPastMatch("(", ")");
			statement("for", level);
		} else if (lexer().peekKeyword("foreach")) {
			lexer().eatToken();
			lexer().readOperator("(");
			lexer().skipPastMatch("(", ")");
			statement("foreach", level);
		} else if (lexer().peekKeyword("fork")) {
			lexer().eatToken();
			
			// Read block identifier
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				lexer().readId();
			}
			
			while (lexer().peek() != null && 
					!lexer().peekKeyword("join", "join_none", "join_any")) {
				debug("--> Fork Statement");
				statement("fork", level);
				debug("<-- Fork Statement");
			}
			// Read join
			lexer().readKeyword("join", "join_none", "join_any");
		} else if (lexer().peekKeyword("case", "casex", "casez")) {
			lexer().eatToken();
			lexer().readOperator("(");
			parsers().SVParser().readExpression();
			lexer().readOperator(")");
			
			while (lexer().peek() != null && !lexer().peekKeyword("endcase")) {
				// Read a series of comma-separated expressions
				while (lexer().peek() != null) {
					parsers().SVParser().readExpression(false);
					if (!lexer().peekOperator(",")) {
						break;
					} else {
						lexer().eatToken();
					}
				}
				lexer().readOperator(":");
				statement("case", level);
			}
			lexer().readKeyword("endcase");
		} else if (lexer().peekKeyword("wait")) {
			lexer().eatToken();
			
			if (lexer().peekKeyword("fork")) {
				lexer().eatToken();
				lexer().readOperator(";");
			} else {
				lexer().readOperator("(");
				parsers().SVParser().readExpression();
				lexer().readOperator(")");
				if (!lexer().peekOperator(";")) {
					statement("wait", level);
				} else {
					lexer().readOperator(";");
				}
			}
		} else if (lexer().peekKeyword("end")) {
			// An unmatched 'end' signals that we're missing some
			// behavioral construct
			error("Unexpected 'end' without matching 'begin' in level " + parent);
		} else if (lexer().peekKeyword("assert")) {
			assertion_stmt(level);
		} else if (ParserSVDBFileFactory.isFirstLevelScope(lexer().peek(), 0) ||
			ParserSVDBFileFactory.isSecondLevelScope(lexer().peek())) {
			error("Unexpected non-behavioral statement keyword " + lexer().peek());
		} else {
			boolean taken = false;
			
			if (lexer().isIdentifier() || lexer().peekOperator(":")) {
				debug(" -- is_identifier @ " + lexer().getStartLocation().getLine());
				if (lexer().peekId()) {
					lexer().eatToken();
				}
				if (lexer().peekOperator(":")) {
					debug("  likely assertion @ " + lexer().getStartLocation().getLine());
					lexer().eatToken();
					if (lexer().peekKeyword("assert")) {
						taken = true;
						assertion_stmt(level);
					}
					// likely an assertion
				}
			}
			
			if (!taken) {
				// Scan to a semi-colon boundary
				while (lexer().peek() != null && !lexer().peekOperator(";")) {
					// Since we're scanning, keep a look out for upper-level scope
					// 
					if (ParserSVDBFileFactory.isFirstLevelScope(lexer().peek(), 0) ||
							ParserSVDBFileFactory.isSecondLevelScope(lexer().peek())) {
							error("Unexpected non-behavioral statement keyword " + lexer().peek());
					}
					lexer().eatToken();
				}
				lexer().readOperator(";");
			}
		}
		debug("<-- [" + level + "] statement " + lexer().peek() + 
				" @ " + lexer().getStartLocation().getLine() + " parent=" + parent);
	}

	private void assertion_stmt(int level) throws SVParseException {
		lexer().readKeyword("assert");
		debug("assertion_stmt - " + lexer().peek());

		if (lexer().peekKeyword("property")) {
			lexer().eatToken();
		}	
		lexer().readOperator("(");
		lexer().skipPastMatch("(", ")");
		statement("assert", level);
	}
}
