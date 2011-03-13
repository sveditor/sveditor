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

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBGenerateBlock;

public class SVGenerateBlockParser extends SVParserBase {
	
	public SVGenerateBlockParser(ISVParser parser) {
		super(parser);
	}
	
	public ISVDBChildItem parse() throws SVParseException {
		if (fLexer.peekKeyword("generate")) {
			return generate_block();
		} else if (fLexer.peekKeyword("if")) {
			return if_block();
		} else if (fLexer.peekKeyword("for")) {
			return for_block();
		} else if (fLexer.peekKeyword("case")) {
			return case_block();
		} else {
			fLexer.readKeyword("generate", "if", "for", "case");
			return null;
		}
	}
	
	public SVDBGenerateBlock generate_block() throws SVParseException {
		SVDBGenerateBlock gen_blk = new SVDBGenerateBlock("");
		gen_blk.setLocation(fLexer.getStartLocation());
		
		fLexer.readKeyword("generate");
		while (fLexer.peek() != null && 
				!fLexer.peekKeyword("endgenerate") && !fLexer.peekKeyword("endmodule")) {
			fParsers.modIfcBodyItemParser().parse("generate");
		}
		
		gen_blk.setEndLocation(fLexer.getStartLocation());
		fLexer.readKeyword("endgenerate");
		
		return gen_blk;
	}
	
	public SVDBGenerateBlock if_block() throws SVParseException {
		SVDBGenerateBlock if_blk = new SVDBGenerateBlock("if");
		parsers().SVParser().enter_scope("generate_if", if_blk);
		fLexer.readKeyword("if");
		fLexer.readOperator("(");
		/*String cond = */parsers().exprParser().expression();
		fLexer.readOperator(")");
		
		if (fLexer.peekKeyword("begin")) {
			fLexer.eatToken();
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
			while (fLexer.peek() != null && !fLexer.peekKeyword("end")) {
				if (fParsers.modIfcBodyItemParser().parse("generate") == null) {
					break;
				}
			}
			fLexer.readKeyword("end");
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
		} else {
			fParsers.modIfcBodyItemParser().parse("generate");
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
					if (fParsers.modIfcBodyItemParser().parse("generate") == null) {
						break;
					}
				}
				fLexer.readKeyword("end");
				if (fLexer.peekOperator(":")) {
					fLexer.eatToken();
					fLexer.readId();
				}
			} else {
				fParsers.modIfcBodyItemParser().parse("generate");
				System.out.println("post-else token: " + fLexer.peek());
			}
		}
		
		parsers().SVParser().handle_leave_scope();
		
		return if_blk;
	}
	
	public SVDBGenerateBlock for_block() throws SVParseException {
		SVDBGenerateBlock gen_blk = new SVDBGenerateBlock("for");
		parsers().SVParser().enter_scope("for", gen_blk);
		
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
		
		if (fLexer.peekKeyword("begin")) {
			fLexer.eatToken();
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
			while (fLexer.peek() != null && !fLexer.peekKeyword("end")) {
				if (fParsers.modIfcBodyItemParser().parse("for") == null) {
					break;
				}
			}
			fLexer.readKeyword("end");
			if (fLexer.peekOperator(":")) {
				fLexer.eatToken();
				fLexer.readId();
			}
		} else {
			fParsers.modIfcBodyItemParser().parse("for");
		}
		
		parsers().SVParser().handle_leave_scope();
		
		return gen_blk;
	}
	
	public SVDBGenerateBlock case_block() throws SVParseException {
		SVDBGenerateBlock case_blk = new SVDBGenerateBlock("case");
		parsers().SVParser().enter_scope("generate_case", case_blk);
		
		fLexer.readKeyword("case");
		fLexer.readOperator("(");
		parsers().exprParser().expression();
		fLexer.readOperator(")");
		
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
					if (fParsers.modIfcBodyItemParser().parse("generate") == null) {
						break;
					}
				}
				
				fLexer.readKeyword("end");
				if (fLexer.peekOperator(":")) {
					fLexer.eatToken();
					fLexer.readId();
				}
			} else {
				if (fParsers.modIfcBodyItemParser().parse("generate") == null) {
					break;
				}
			}
		}

		fLexer.readKeyword("endcase");
		
		parsers().SVParser().handle_leave_scope();

		return case_blk;
	}

}
