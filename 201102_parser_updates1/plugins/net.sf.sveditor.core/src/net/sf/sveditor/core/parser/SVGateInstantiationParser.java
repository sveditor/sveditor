package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;

public class SVGateInstantiationParser extends SVParserBase {
	
	public SVGateInstantiationParser(ISVParser parser) {
		super(parser);
	}
	
	public List<SVDBModIfcInstItem> parse() throws SVParseException {
		List<SVDBModIfcInstItem> ret = new ArrayList<SVDBModIfcInstItem>();
		SVDBModIfcInstItem item;
		
		if (lexer().peekKeyword("cmos", "rcmos")) {
			// cmos gates have 4 terminals
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(lexer().eatToken());
			
			if (lexer().peekOperator("#")) {
				// TODO: handle/store delay somewhere
				parsers().SVParser().delay3();
			}
			
			// Now, a series of switch instances
			while (lexer().peek() != null) {
				String name = ""; 
				if (lexer().peekId()) {
					name = lexer().eatToken();
				}
				item = new SVDBModIfcInstItem(type, name);
				ret.add(item);
				
				lexer().readOperator("(");
				
				// TODO: output_terminal
				parsers().exprParser().expression();
				
				lexer().readOperator(",");
				
				// TODO: input_terminal
				parsers().exprParser().expression();
				
				lexer().readOperator(",");
				
				// TODO: ncontrol_terminal
				parsers().exprParser().expression();
				lexer().readOperator(",");

				// TODO: pcontrol_terminal
				parsers().exprParser().expression();

				lexer().readOperator(")");
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		} else if (lexer().peekKeyword("bufif0","bufif1","notif0","notif1",
				"nmos", "pmos", "rnmos", "rpmos")) {
			// enable or mos gate instance
			// Both have three terminals
			
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(lexer().eatToken());
			if (lexer().peekOperator("#")) {
				// TODO: handle/store delay somewhere
				parsers().SVParser().delay3();
			}
			
			// Now, a series of switch instances
			while (lexer().peek() != null) {
				String name = ""; 
				if (lexer().peekId()) {
					name = lexer().eatToken();
				}
				item = new SVDBModIfcInstItem(type, name);
				ret.add(item);
				
				lexer().readOperator("(");
				
				// TODO: output_terminal
				parsers().exprParser().expression();
				lexer().readOperator(",");
				
				// TODO: input_terminal
				parsers().exprParser().expression();
				lexer().readOperator(",");
				
				// TODO: enable_terminal
				parsers().exprParser().expression();

				lexer().readOperator(")");
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		} else if (lexer().peekKeyword("and", "nand", "or", "nor", "xor", "xnor",
				"buf", "not")) {
			// N-input or N-output gate instances
			// Essentially, all appear to have a variable number of terminals
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(lexer().eatToken());
			if (lexer().peekOperator("#")) {
				// TODO: handle/store delay somewhere
				parsers().SVParser().delay3();
			}

			// Now, a series of switch instances
			while (lexer().peek() != null) {
				String name = ""; 
				if (lexer().peekId()) {
					name = lexer().eatToken();
				}
				item = new SVDBModIfcInstItem(type, name);
				ret.add(item);
				
				lexer().readOperator("(");
				
				// TODO: output_terminal
				parsers().exprParser().expression();
				lexer().readOperator(",");
				
				// TODO: input_terminal
				parsers().exprParser().expression();
				
				while (lexer().peekOperator(",")) {
					lexer().eatToken();
					// TODO: extra terminals
					parsers().exprParser().expression();
				}

				lexer().readOperator(")");
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		} else if (lexer().peekKeyword("tran", "rtran")) {
			// Pass switches have two terminals
			
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(lexer().eatToken());
			
			if (lexer().peekOperator("#")) {
				// TODO: handle/store delay somewhere
				parsers().SVParser().delay3();
			}

			// Now, a series of switch instances
			while (lexer().peek() != null) {
				String name = ""; 
				if (lexer().peekId()) {
					name = lexer().eatToken();
				}
				item = new SVDBModIfcInstItem(type, name);
				ret.add(item);
				
				lexer().readOperator("(");
				
				// TODO: inout_terminal
				parsers().exprParser().expression();
				lexer().readOperator(",");
				
				// TODO: inout_terminal
				parsers().exprParser().expression();
				
				lexer().readOperator(")");
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		} else if (lexer().peekKeyword("tranif0", "tranif1", "rtranif1", "rtranif0")) {
			// Enable pass-switches have three terminals
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(lexer().eatToken());
			
			if (lexer().peekOperator("#")) {
				// TODO: handle/store delay somewhere
				parsers().SVParser().delay3();
			}

			// Now, a series of switch instances
			while (lexer().peek() != null) {
				String name = ""; 
				if (lexer().peekId()) {
					name = lexer().eatToken();
				}
				item = new SVDBModIfcInstItem(type, name);
				ret.add(item);
				
				lexer().readOperator("(");
				
				// TODO: inout_terminal
				parsers().exprParser().expression();
				lexer().readOperator(",");
				
				// TODO: inout_terminal
				parsers().exprParser().expression();
				lexer().readOperator(",");

				parsers().exprParser().expression();

				lexer().readOperator(")");
				
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		} else if (lexer().peekKeyword("pullup", "pulldown")) {
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(lexer().eatToken());
			
			// TODO: still handling pull-ups lexically
			if (lexer().peekOperator("(")) {
				lexer().skipPastMatch("(", ")");
			}
			while (lexer().peek() != null && !lexer().peekOperator(";")) {
				lexer().readIdOrKeyword(); // pullup
				lexer().readOperator("(");
				lexer().skipPastMatch("(", ")");
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		} else {
			error("[Internal Error] gate-type " + lexer().peek() + " not recognized");
		}
		
		lexer().readOperator(";");
		
		return ret;
	}

}
