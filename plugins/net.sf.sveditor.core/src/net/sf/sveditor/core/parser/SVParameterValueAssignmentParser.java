package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.SVDBParamValueAssign;
import net.sf.sveditor.core.db.SVDBParamValueAssignList;

public class SVParameterValueAssignmentParser extends SVParserBase {
	
	public SVParameterValueAssignmentParser(ISVParser parser) {
		super(parser);
	}
	
	public SVDBParamValueAssignList parse() throws SVParseException {
		SVDBParamValueAssignList ret = new SVDBParamValueAssignList();
		StringBuilder v = new StringBuilder();
		
		lexer().readOperator("#");
		lexer().readOperator("(");
		while (true) {
			boolean is_mapped = false;
			String name = null;
			if (lexer().peekOperator(".")) {
				lexer().eatToken();
				name = lexer().readId();
				lexer().readOperator("(");
				is_mapped = true;
			}

			if (is_mapped) {
				// Read inside
				lexer().readOperator(")");
			}
			
			v.setLength(0);
			while (true) {
				if (lexer().peekOperator("(")) {
					int lb_cnt = 1, rb_cnt = 0;
					v.append("(");
					while (lb_cnt != rb_cnt) {
						if (lexer().peekOperator("(")) {
							lb_cnt++;
						} else if (lexer().peekOperator(")")) {
							rb_cnt++;
						} else if (lexer().peekOperator(";")) {
							break; // escape
						}
						v.append(lexer().eatToken());
					}
				} else if (lexer().peekOperator(",", ")")) {
					break;
				} else {
					v.append(lexer().eatToken());
				}
			}
			ret.addParameter(new SVDBParamValueAssign(name, v.toString()));
			ret.setIsNamedMapping(is_mapped);
			
			if (lexer().peekOperator(",")) {
				lexer().eatToken();
			} else {
				break;
			}
		}
		
		lexer().readOperator(")");
		
		return ret;
	}

}
