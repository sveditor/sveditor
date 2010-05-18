package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBTaskFuncParam;
import net.sf.sveditor.core.db.SVDBTypeInfo;

public class SVTaskFunctionPortListParser extends SVParserBase {
	
	public SVTaskFunctionPortListParser(ISVParser parser) {
		super(parser);
	}
	
	public List<SVDBTaskFuncParam> parse() throws SVParseException {
		List<SVDBTaskFuncParam> params = new ArrayList<SVDBTaskFuncParam>();
		int dir = SVDBTaskFuncParam.Direction_Input;
		
		lexer().readOperator("(");
		
		// Empty parameter list
		if (lexer().peekOperator(")")) {
			lexer().eatToken();
			return params;
		}
		
		while (true) {
			if (lexer().peekKeyword("input", "output", "inout", "ref")) {
				String dir_s = lexer().eatToken();
				if (dir_s.equals("input")) {
					dir = SVDBTaskFuncParam.Direction_Input;
				} else if (dir_s.equals("output")) {
					dir = SVDBTaskFuncParam.Direction_Output;
				} else if (dir_s.equals("inout")) {
					dir = SVDBTaskFuncParam.Direction_Inout;
				} else if (dir_s.equals("ref")) {
					dir = SVDBTaskFuncParam.Direction_Ref;
				}
			} else if (lexer().peekKeyword("const")) {
				lexer().eatToken();
				lexer().readKeyword("ref");
				dir = (SVDBTaskFuncParam.Direction_Ref | SVDBTaskFuncParam.Direction_Const);
			}
			
			if (lexer().peekKeyword("var")) {
				lexer().eatToken();
				dir |= SVDBTaskFuncParam.Direction_Var;
			}
			
			SVDBTypeInfo type = 
				parsers().dataTypeParser().data_type(lexer().eatToken());
			
			String id = lexer().readId();
			
			SVDBTaskFuncParam param = new SVDBTaskFuncParam(type, id);
			param.setDir(dir);
			
			params.add(param);
			
			if (lexer().peekOperator(",")) {
				lexer().eatToken();
			} else {
				break;
			}
		}
		
		lexer().readOperator(")");
		
		return params;
	}

}
