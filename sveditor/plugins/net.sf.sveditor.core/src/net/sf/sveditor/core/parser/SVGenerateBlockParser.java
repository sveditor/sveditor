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
		if (fLexer.peekKeyword("generate")) {
			generate_block(parent);
		} else if (fLexer.peekKeyword("if")) {
			if_block(parent);
		} else if (fLexer.peekKeyword("for")) {
			for_block(parent);
		} else if (fLexer.peekKeyword("case")) {
			case_block(parent);
		} else {
			fLexer.readKeyword("generate", "if", "for", "case");
		}
	}
	
	public void generate_block(ISVDBAddChildItem parent) throws SVParseException {
		SVDBGenerateBlock gen_blk = new SVDBGenerateBlock("");
		gen_blk.setLocation(fLexer.getStartLocation());
		
		fLexer.readKeyword("generate");
		
		parent.addChildItem(gen_blk);
		while (fLexer.peek() != null && 
				!fLexer.peekKeyword("endgenerate") && !fLexer.peekKeyword("endmodule")) {
			if (fLexer.peekKeyword("begin")) {
				gen_blk.fName = begin_end_block(gen_blk);
			} else {
				fParsers.modIfcBodyItemParser().parse(gen_blk, "generate");
			}
		}
		
		gen_blk.setEndLocation(fLexer.getStartLocation());
		fLexer.readKeyword("endgenerate");
		
	}
	
	private String begin_end_block(ISVDBAddChildItem parent) throws SVParseException {
		String thename = null;
		fLexer.readKeyword("begin");
		if (fLexer.peekOperator(":")) {
			fLexer.eatToken();
			thename = fLexer.readId();
		}
		while (fLexer.peek() != null && !fLexer.peekKeyword("end")) {
			fParsers.modIfcBodyItemParser().parse(parent, "generate");
		}
		fLexer.readKeyword("end");
		if (fLexer.peekOperator(":")) {
			fLexer.eatToken();
			fLexer.readId();
		}
		return thename;
	}
	
	public void if_block(ISVDBAddChildItem parent) throws SVParseException {
		SVDBGenerateIf if_blk = new SVDBGenerateIf();
		if_blk.setLocation(fLexer.getStartLocation());
		fLexer.readKeyword("if");
		fLexer.readOperator("(");
		if_blk.setExpr(parsers().exprParser().expression());
		fLexer.readOperator(")");
		
		parent.addChildItem(if_blk);
		
		if (fLexer.peekKeyword("begin")) {
			if_blk.fName = "if";
			String strng = begin_end_block(if_blk);
			if (strng != null)  {
				if_blk.fName += ": " + strng;
			}
			/*
			fLexer.eatToken();
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
			while (fLexer.peek() != null && !fLexer.peekKeyword("end")) {
				fParsers.modIfcBodyItemParser().parse(if_blk, "generate");
			}
			fLexer.readKeyword("end");
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
			 */
		} else {
			fParsers.modIfcBodyItemParser().parse(if_blk, "generate");
		}
		
		if (fLexer.peekKeyword("else")) {
			fLexer.eatToken();
			if (fLexer.peekKeyword("begin")) {
				fLexer.eatToken();
				if (fLexer.peekOperator(":")) {
					fLexer.eatToken();
					fLexer.readId();
				}
				while (fLexer.peek() != null && !fLexer.peekKeyword("end")) {
					fParsers.modIfcBodyItemParser().parse(if_blk, "generate");
				}
				fLexer.readKeyword("end");
				if (fLexer.peekOperator(":")) {
					fLexer.eatToken();
					fLexer.readId();
				}
			} else {
				fParsers.modIfcBodyItemParser().parse(if_blk, "generate");
			}
		}
	}
	
	public void for_block(ISVDBAddChildItem parent) throws SVParseException {
		SVDBGenerateBlock gen_blk = new SVDBGenerateBlock("for");
		boolean nested_begin = false;
		
		fLexer.readKeyword("for");
		fLexer.readOperator("(");
		if (fLexer.peekKeyword("genvar")) {
			fLexer.eatToken();
		}
		if (!fLexer.peekOperator(";")) {
			/*String init = */parsers().exprParser().expression();
		}
		fLexer.readOperator(";");
		if (!fLexer.peekOperator(";")) {
			/*String cond = */parsers().exprParser().expression();
		}
		fLexer.readOperator(";");
		if (!fLexer.peekOperator(")")) {
			/*String incr = */parsers().exprParser().expression();
		}
		fLexer.readOperator(")");

		parent.addChildItem(gen_blk);

		if (fLexer.peekKeyword("begin")) {
			gen_begin_end(gen_blk);
		} else {
			fParsers.modIfcBodyItemParser().parse(gen_blk, "for");
		}
	}

	public void gen_begin_end(ISVDBAddChildItem parent) throws SVParseException {
		SVDBGenerateBlock gen_blk = new SVDBGenerateBlock("begin");
		parent.addChildItem(gen_blk);
		
		fLexer.readKeyword("begin");
		if (fLexer.peekOperator(":")) {
			fLexer.eatToken();
			gen_blk.setName(fLexer.readId());
		}

		while (fLexer.peek() != null && !fLexer.peekKeyword("end")) {
			if (fLexer.peekKeyword("begin")) {
				gen_begin_end(gen_blk);
			} else {
				fParsers.modIfcBodyItemParser().parse(gen_blk, "begin");
			}
		}
	
		fLexer.readKeyword("end");
		if (fLexer.peekOperator(":")) {
			fLexer.eatToken();
			fLexer.readId();
		}		
	}
	
	public void case_block(ISVDBAddChildItem parent) throws SVParseException {
		SVDBGenerateBlock case_blk = new SVDBGenerateBlock("case");
		
		fLexer.readKeyword("case");
		fLexer.readOperator("(");
		parsers().exprParser().expression();
		fLexer.readOperator(")");
		
		parent.addChildItem(case_blk);
		
		while (fLexer.peek() != null && !fLexer.peekKeyword("endcase")) {
			if (fLexer.peekKeyword("default")) {
				fLexer.eatToken();
			} else {
				// Read list of expressions
				do {
					if (fLexer.peekOperator(",")) {
						fLexer.eatToken();
					}
					parsers().exprParser().expression();
				} while (fLexer.peekOperator(","));
			}
			fLexer.readOperator(":");
			
			if (fLexer.peekKeyword("begin")) {
				fLexer.eatToken();
				if (fLexer.peekOperator(":")) {
					fLexer.eatToken();
					fLexer.readId();
				}
				
				while (fLexer.peek() != null && !fLexer.peekKeyword("end")) {
					fParsers.modIfcBodyItemParser().parse(case_blk, "generate");
				}
				
				fLexer.readKeyword("end");
				if (fLexer.peekOperator(":")) {
					fLexer.eatToken();
					fLexer.readId();
				}
			} else {
				generate_item(case_blk);
			}
		}

		fLexer.readKeyword("endcase");
	}

	private void generate_item(ISVDBAddChildItem blk) throws SVParseException {
		SVToken tok = fLexer.consumeToken();
		
		if (tok.isIdentifier() && fLexer.peekOperator("(")) {
			fLexer.ungetToken(tok);
			fParsers.behavioralBlockParser().statement(blk);
		} else {
			fLexer.ungetToken(tok);
			fParsers.modIfcBodyItemParser().parse(blk, "generate");
		}
	}
}
