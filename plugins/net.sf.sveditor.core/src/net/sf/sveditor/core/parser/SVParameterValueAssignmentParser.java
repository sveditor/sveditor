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
			
			String val = parsers().SVParser().readExpression();

			if (is_mapped) {
				// Read inside
				lexer().readOperator(")");
			}

			/*
			v.setLength(0);
			while (lexer().peek() != null) {
				if (lexer().peekOperator("#")) {
					lexer().eatToken();
					lexer().readOperator("(");
					lexer().startCapture();
					lexer().skipPastMatch("(", ")", ";");
					v.append(lexer().endCapture());
				} else if (lexer().peekOperator("(")) {
					lexer().startCapture();
					lexer().skipPastMatch("(", ")", ";");
					v.append(lexer().endCapture());
				} else if (lexer().peekOperator(",", ")")) {
					break;
				} else {
					v.append(lexer().eatToken());
				}
			}
			 */
			//ret.addParameter(new SVDBParamValueAssign(name, v.toString()));
			ret.addParameter(new SVDBParamValueAssign(name, val));
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
