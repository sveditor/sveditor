package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBTypeInfoUserDef;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVGateInstantiationParser extends SVParserBase {
	
	public SVGateInstantiationParser(ISVParser parser) {
		super(parser);
	}
	
	public List<SVDBModIfcInst> parse() throws SVParseException {
		List<SVDBModIfcInst> ret = new ArrayList<SVDBModIfcInst>();
		SVDBModIfcInst item;
		
		if (fLexer.peekKeyword("cmos", "rcmos")) {
			// cmos gates have 4 terminals
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(fLexer.eatToken());
			
			if (fLexer.peekOperator("#")) {
				// TODO: handle/store delay somewhere
				parsers().SVParser().delay3();
			}
			
			// Now, a series of switch instances
			while (fLexer.peek() != null) {
				String name = ""; 
				if (fLexer.peekId()) {
					name = fLexer.eatToken();
				}
				item = new SVDBModIfcInst(type, name);
				ret.add(item);
				
				fLexer.readOperator("(");
				
				// TODO: output_terminal
				parsers().exprParser().expression();
				
				fLexer.readOperator(",");
				
				// TODO: input_terminal
				parsers().exprParser().expression();
				
				fLexer.readOperator(",");
				
				// TODO: ncontrol_terminal
				parsers().exprParser().expression();
				fLexer.readOperator(",");

				// TODO: pcontrol_terminal
				parsers().exprParser().expression();

				fLexer.readOperator(")");
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		} else if (fLexer.peekKeyword("bufif0","bufif1","notif0","notif1",
				"nmos", "pmos", "rnmos", "rpmos")) {
			// enable or mos gate instance
			// Both have three terminals
			
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(fLexer.eatToken());
			if (fLexer.peekOperator("#")) {
				// TODO: handle/store delay somewhere
				parsers().SVParser().delay3();
			}
			
			// Now, a series of switch instances
			while (fLexer.peek() != null) {
				String name = ""; 
				if (fLexer.peekId()) {
					name = fLexer.eatToken();
				}
				item = new SVDBModIfcInst(type, name);
				ret.add(item);
				
				fLexer.readOperator("(");
				
				// TODO: output_terminal
				parsers().exprParser().expression();
				fLexer.readOperator(",");
				
				// TODO: input_terminal
				parsers().exprParser().expression();
				fLexer.readOperator(",");
				
				// TODO: enable_terminal
				parsers().exprParser().expression();

				fLexer.readOperator(")");
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		} else if (fLexer.peekKeyword("and", "nand", "or", "nor", "xor", "xnor",
				"buf", "not")) {
			// N-input or N-output gate instances
			// Essentially, all appear to have a variable number of terminals
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(fLexer.eatToken());
			if (fLexer.peekOperator("#")) {
				// TODO: handle/store delay somewhere
				parsers().SVParser().delay3();
			}

			// Now, a series of switch instances
			while (fLexer.peek() != null) {
				String name = ""; 
				if (fLexer.peekId()) {
					name = fLexer.eatToken();
				}
				item = new SVDBModIfcInst(type, name);
				ret.add(item);
				
				fLexer.readOperator("(");
				
				// TODO: output_terminal
				parsers().exprParser().expression();
				fLexer.readOperator(",");
				
				// TODO: input_terminal
				parsers().exprParser().expression();
				
				while (fLexer.peekOperator(",")) {
					fLexer.eatToken();
					// TODO: extra terminals
					parsers().exprParser().expression();
				}

				fLexer.readOperator(")");
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		} else if (fLexer.peekKeyword("tran", "rtran")) {
			// Pass switches have two terminals
			
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(fLexer.eatToken());
			
			if (fLexer.peekOperator("#")) {
				// TODO: handle/store delay somewhere
				parsers().SVParser().delay3();
			}

			// Now, a series of switch instances
			while (fLexer.peek() != null) {
				String name = ""; 
				if (fLexer.peekId()) {
					name = fLexer.eatToken();
				}
				item = new SVDBModIfcInst(type, name);
				ret.add(item);
				
				fLexer.readOperator("(");
				
				// TODO: inout_terminal
				parsers().exprParser().expression();
				fLexer.readOperator(",");
				
				// TODO: inout_terminal
				parsers().exprParser().expression();
				
				fLexer.readOperator(")");
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		} else if (fLexer.peekKeyword("tranif0", "tranif1", "rtranif1", "rtranif0")) {
			// Enable pass-switches have three terminals
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(fLexer.eatToken());
			
			if (fLexer.peekOperator("#")) {
				// TODO: handle/store delay somewhere
				parsers().SVParser().delay3();
			}

			// Now, a series of switch instances
			while (fLexer.peek() != null) {
				String name = ""; 
				if (fLexer.peekId()) {
					name = fLexer.eatToken();
				}
				item = new SVDBModIfcInst(type, name);
				ret.add(item);
				
				fLexer.readOperator("(");
				
				// TODO: inout_terminal
				parsers().exprParser().expression();
				fLexer.readOperator(",");
				
				// TODO: inout_terminal
				parsers().exprParser().expression();
				fLexer.readOperator(",");

				parsers().exprParser().expression();

				fLexer.readOperator(")");
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		} else if (fLexer.peekKeyword("pullup", "pulldown")) {
			SVDBTypeInfoUserDef type = new SVDBTypeInfoUserDef(fLexer.eatToken());
			
			if (fLexer.peekOperator("(")) {
				fLexer.readOperator("(");
				fLexer.readKeyword(SVKeywords.fStrength);
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
					fLexer.readKeyword(SVKeywords.fStrength);
				}
				
				fLexer.readOperator(")");
			}

			while (fLexer.peek() != null) {
				item = new SVDBModIfcInst(type, fLexer.readId());
				ret.add(item);
				
				fLexer.readOperator("(");
				parsers().exprParser().expression();
				fLexer.readOperator(")");
				
				if (fLexer.peekOperator(",")) {
					fLexer.eatToken();
				} else {
					break;
				}
			}
		} else {
			error("[Internal Error] gate-type " + fLexer.peek() + " not recognized");
		}
		
		fLexer.readOperator(";");
		
		return ret;
	}

}
