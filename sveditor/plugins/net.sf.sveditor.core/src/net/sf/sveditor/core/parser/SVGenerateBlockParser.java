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


package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBGenerateBlock;
import net.sf.sveditor.core.db.SVDBGenerateIf;

public class SVGenerateBlockParser extends SVParserBase {
	
	public SVGenerateBlockParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(ISVDBAddChildItem parent) throws SVParseException {
		KW kw = fLexer.peekKeywordE();
		
		if (kw == KW.GENERATE) {
			generate_block(parent);
		} else if (kw == KW.IF) {
			if_block(parent);
		} else if (kw == KW.FOR) {
			for_block(parent);
		} else if (kw == KW.CASE) {
			case_block(parent);
		} else {
			fLexer.readKeyword(KW.GENERATE, KW.IF, KW.FOR, KW.CASE);
		}
	}
	
	public void generate_block(ISVDBAddChildItem parent) throws SVParseException {
		SVDBGenerateBlock gen_blk = new SVDBGenerateBlock("");
		gen_blk.setLocation(fLexer.getStartLocation());
		
		fLexer.readKeyword(KW.GENERATE);
		
		parent.addChildItem(gen_blk);
		while (fLexer.peek() != null && !fLexer.peekKeyword(KW.ENDGENERATE, KW.ENDMODULE)) {
			if (fLexer.peekKeyword(KW.BEGIN)) {
				gen_blk.fName = begin_end_block(gen_blk);
			} else {
				fParsers.modIfcBodyItemParser().parse(gen_blk);
			}
		}
		
		gen_blk.setEndLocation(fLexer.getStartLocation());
		fLexer.readKeyword(KW.ENDGENERATE);
		
	}
	
	private String begin_end_block(ISVDBAddChildItem parent) throws SVParseException {
		String thename = null;
		fLexer.readKeyword(KW.BEGIN);
		if (fLexer.peekOperator(OP.COLON)) {
			fLexer.eatToken();
			thename = fLexer.readId();
		}
		while (fLexer.peek() != null && !fLexer.peekKeyword(KW.END)) {
			fParsers.modIfcBodyItemParser().parse(parent);
		}
		fLexer.readKeyword(KW.END);
		if (fLexer.peekOperator(OP.COLON)) {
			fLexer.eatToken();
			fLexer.readId();
		}
		return thename;
	}
	
	public void if_block(ISVDBAddChildItem parent) throws SVParseException {
		SVDBGenerateIf if_blk = new SVDBGenerateIf();
		if_blk.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword(KW.IF);
		fLexer.readOperator(OP.LPAREN);
		if_blk.setExpr(parsers().exprParser().expression());
		fLexer.readOperator(OP.RPAREN);
		
		parent.addChildItem(if_blk);
		
		if (fLexer.peekKeyword(KW.BEGIN)) {
			if_blk.fName = "if";
			String strng = begin_end_block(if_blk);
			if (strng != null)  {
				if_blk.fName += ": " + strng;
			}
			/*
			fLexer.eatToken();
			if (fLexer.peekOperator(OP.COLON)) {
				fLexer.eatToken();
				fLexer.readId();
			}
			while (fLexer.peek() != null && !fLexer.peekKeyword(KW.END)) {
				fParsers.modIfcBodyItemParser().parse(if_blk, "generate");
			}
			fLexer.readKeyword(KW.END);
			if (fLexer.peekOperator(OP.COLON)) {
				fLexer.eatToken();
				fLexer.readId();
			}
			 */
		} else {
			fParsers.modIfcBodyItemParser().parse(if_blk);
		}
		
		if (fLexer.peekKeyword(KW.ELSE)) {
			fLexer.eatToken();
			if (fLexer.peekKeyword(KW.BEGIN)) {
				fLexer.eatToken();
				if (fLexer.peekOperator(OP.COLON)) {
					fLexer.eatToken();
					fLexer.readId();
				}
				while (fLexer.peek() != null && !fLexer.peekKeyword(KW.END)) {
					fParsers.modIfcBodyItemParser().parse(if_blk);
				}
				fLexer.readKeyword(KW.END);
				if (fLexer.peekOperator(OP.COLON)) {
					fLexer.eatToken();
					fLexer.readId();
				}
			} else {
				fParsers.modIfcBodyItemParser().parse(if_blk);
			}
		}
	}
	
	public void for_block(ISVDBAddChildItem parent) throws SVParseException {
		SVDBGenerateBlock gen_blk = new SVDBGenerateBlock("for");
		gen_blk.setLocation(fLexer.getStartLocation());
		boolean nested_begin = false;
		
		fLexer.readKeyword(KW.FOR);
		fLexer.readOperator(OP.LPAREN);
		if (fLexer.peekKeyword(KW.GENVAR)) {
			fLexer.eatToken();
		}
		if (!fLexer.peekOperator(OP.SEMICOLON)) {
			/*String init = */parsers().exprParser().expression();
		}
		fLexer.readOperator(OP.SEMICOLON);
		if (!fLexer.peekOperator(OP.SEMICOLON)) {
			/*String cond = */parsers().exprParser().expression();
		}
		fLexer.readOperator(OP.SEMICOLON);
		if (!fLexer.peekOperator(OP.RPAREN)) {
			/*String incr = */parsers().exprParser().expression();
		}
		fLexer.readOperator(OP.RPAREN);

		parent.addChildItem(gen_blk);

		if (fLexer.peekKeyword(KW.BEGIN)) {
			gen_begin_end(gen_blk);
		} else {
			fParsers.modIfcBodyItemParser().parse(gen_blk);
		}
	}

	public void gen_begin_end(ISVDBAddChildItem parent) throws SVParseException {
		SVDBGenerateBlock gen_blk = new SVDBGenerateBlock("begin");
		gen_blk.setLocation(fLexer.getStartLocation());
		parent.addChildItem(gen_blk);
		
		fLexer.readKeyword(KW.BEGIN);
		if (fLexer.peekOperator(OP.COLON)) {
			fLexer.eatToken();
			gen_blk.setName(fLexer.readId());
		}

		while (fLexer.peek() != null && !fLexer.peekKeyword(KW.END)) {
			if (fLexer.peekKeyword(KW.BEGIN)) {
				gen_begin_end(gen_blk);
			} else {
				fParsers.modIfcBodyItemParser().parse(gen_blk);
			}
		}
	
		fLexer.readKeyword(KW.END);
		if (fLexer.peekOperator(OP.COLON)) {
			fLexer.eatToken();
			fLexer.readId();
		}		
	}
	
	public void case_block(ISVDBAddChildItem parent) throws SVParseException {
		SVDBGenerateBlock case_blk = new SVDBGenerateBlock("case");
		
		fLexer.readKeyword(KW.CASE);
		fLexer.readOperator(OP.LPAREN);
		parsers().exprParser().expression();
		fLexer.readOperator(OP.RPAREN);
		
		parent.addChildItem(case_blk);
		
		while (fLexer.peek() != null && !fLexer.peekKeyword(KW.ENDCASE)) {
			if (fLexer.peekKeyword(KW.DEFAULT)) {
				fLexer.eatToken();
			} else {
				// Read list of expressions
				do {
					if (fLexer.peekOperator(OP.COMMA)) {
						fLexer.eatToken();
					}
					parsers().exprParser().expression();
				} while (fLexer.peekOperator(OP.COMMA));
			}
			fLexer.readOperator(OP.COLON);
			
			if (fLexer.peekKeyword(KW.BEGIN)) {
				fLexer.eatToken();
				if (fLexer.peekOperator(OP.COLON)) {
					fLexer.eatToken();
					fLexer.readId();
				}
				
				while (fLexer.peek() != null && !fLexer.peekKeyword(KW.END)) {
					fParsers.modIfcBodyItemParser().parse(case_blk);
				}
				
				fLexer.readKeyword(KW.END);
				if (fLexer.peekOperator(OP.COLON)) {
					fLexer.eatToken();
					fLexer.readId();
				}
			} else {
				generate_item(case_blk);
			}
		}

		fLexer.readKeyword(KW.ENDCASE);
	}

	private void generate_item(ISVDBAddChildItem blk) throws SVParseException {
		SVToken tok = fLexer.consumeToken();
		
		if (tok.isIdentifier() && fLexer.peekOperator(OP.LPAREN)) {
			fLexer.ungetToken(tok);
			fParsers.behavioralBlockParser().statement(blk);
		} else {
			fLexer.ungetToken(tok);
			fParsers.modIfcBodyItemParser().parse(blk);
		}
	}
}
