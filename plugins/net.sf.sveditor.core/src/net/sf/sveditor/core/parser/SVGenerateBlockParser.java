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

import net.sf.sveditor.core.db.SVDBGenerateBlock;

public class SVGenerateBlockParser extends SVParserBase {
	
	public SVGenerateBlockParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBGenerateBlock generate_block() throws SVParseException {
		SVDBGenerateBlock gen_blk = new SVDBGenerateBlock("");
		gen_blk.setLocation(lexer().getStartLocation());
		
		lexer().readKeyword("generate");
		while (lexer().peek() != null && 
				!lexer().peekKeyword("endgenerate") && !lexer().peekKeyword("endmodule")) {
			parsers().SVParser().process_module_class_interface_body_item("generate");
		}
		
		gen_blk.setEndLocation(lexer().getStartLocation());
		lexer().readKeyword("endgenerate");
		
		return gen_blk;
	}
	
	public SVDBGenerateBlock if_block() throws SVParseException {
		SVDBGenerateBlock if_blk = new SVDBGenerateBlock("if");
		parsers().SVParser().enter_scope("generate_if", if_blk);
		lexer().readKeyword("if");
		lexer().readOperator("(");
		/*String cond = */parsers().exprParser().expression();
		lexer().readOperator(")");
		
		if (lexer().peekKeyword("begin")) {
			lexer().eatToken();
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				lexer().readId();
			}
			while (lexer().peek() != null && !lexer().peekKeyword("end")) {
				if (parsers().SVParser().process_module_class_interface_body_item("generate") == null) {
					break;
				}
			}
			lexer().readKeyword("end");
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				lexer().readId();
			}
		} else {
			parsers().SVParser().process_module_class_interface_body_item("generate");
		}
		
		if (lexer().peekKeyword("else")) {
			lexer().eatToken();
			if (lexer().peekKeyword("begin")) {
				lexer().eatToken();
				if (lexer().peekOperator(":")) {
					lexer().eatToken();
					lexer().readId();
				}
				while (lexer().peek() != null && !lexer().peekKeyword("end")) {
					if (parsers().SVParser().process_module_class_interface_body_item("generate") == null) {
						break;
					}
				}
				lexer().readKeyword("end");
				if (lexer().peekOperator(":")) {
					lexer().eatToken();
					lexer().readId();
				}
			} else {
				parsers().SVParser().process_module_class_interface_body_item("generate");
				System.out.println("post-else token: " + lexer().peek());
			}
		}
		
		parsers().SVParser().handle_leave_scope();
		
		return if_blk;
	}
	
	public SVDBGenerateBlock for_block() throws SVParseException {
		SVDBGenerateBlock gen_blk = new SVDBGenerateBlock("for");
		parsers().SVParser().enter_scope("for", gen_blk);
		
		lexer().readKeyword("for");
		lexer().readOperator("(");
		if (lexer().peekKeyword("genvar")) {
			lexer().eatToken();
		}
		if (!lexer().peekOperator(";")) {
			/*String init = */parsers().exprParser().expression();
		}
		lexer().readOperator(";");
		if (!lexer().peekOperator(";")) {
			/*String cond = */parsers().exprParser().expression();
		}
		lexer().readOperator(";");
		if (!lexer().peekOperator(")")) {
			/*String incr = */parsers().exprParser().expression();
		}
		lexer().readOperator(")");
		
		if (lexer().peekKeyword("begin")) {
			lexer().eatToken();
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				lexer().readId();
			}
			while (lexer().peek() != null && !lexer().peekKeyword("end")) {
				if (parsers().SVParser().process_module_class_interface_body_item("for") == null) {
					break;
				}
			}
			lexer().readKeyword("end");
			if (lexer().peekOperator(":")) {
				lexer().eatToken();
				lexer().readId();
			}
		} else {
			parsers().SVParser().process_module_class_interface_body_item("for");
		}
		
		parsers().SVParser().handle_leave_scope();
		
		return gen_blk;
	}
	
	public SVDBGenerateBlock case_block() throws SVParseException {
		SVDBGenerateBlock case_blk = new SVDBGenerateBlock("case");
		parsers().SVParser().enter_scope("generate_case", case_blk);
		
		lexer().readKeyword("case");
		lexer().readOperator("(");
		parsers().exprParser().expression();
		lexer().readOperator(")");
		
		while (lexer().peek() != null && !lexer().peekKeyword("endcase")) {
			if (lexer().peekKeyword("default")) {
				lexer().eatToken();
			} else {
				// Read list of expressions
				do {
					if (lexer().peekOperator(",")) {
						lexer().eatToken();
					}
					parsers().exprParser().expression(false);
				} while (lexer().peekOperator(","));
			}
			lexer().readOperator(":");
			
			if (lexer().peekKeyword("begin")) {
				lexer().eatToken();
				if (lexer().peekOperator(":")) {
					lexer().eatToken();
					lexer().readId();
				}
				
				while (lexer().peek() != null && !lexer().peekKeyword("end")) {
					if (parsers().SVParser().process_module_class_interface_body_item("generate") == null) {
						break;
					}
				}
				
				lexer().readKeyword("end");
				if (lexer().peekOperator(":")) {
					lexer().eatToken();
					lexer().readId();
				}
			} else {
				if (parsers().SVParser().process_module_class_interface_body_item("generate") == null) {
					break;
				}
			}
		}

		lexer().readKeyword("endcase");
		
		parsers().SVParser().handle_leave_scope();

		return case_blk;
	}

}
