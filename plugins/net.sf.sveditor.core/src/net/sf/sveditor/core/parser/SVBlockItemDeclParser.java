package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBVarDeclItem;

public class SVBlockItemDeclParser extends SVParserBase {
	
	public SVBlockItemDeclParser(ISVParser parser) {
		super(parser);
	}
	
	public List<SVDBItem> parse() throws SVParseException {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		if (lexer().peekKeyword("const")) {
			lexer().eatToken();
		}
		if (lexer().peekKeyword("var")) {
			lexer().eatToken();
		}

		if (lexer().peekKeyword("static", "automatic")) {
			lexer().eatToken();
		}
		
		// Should be the data-type
		SVDBTypeInfo type = parsers().dataTypeParser().data_type(lexer().eatToken());
		
		while (true) {
			String name = lexer().readId();
			
			SVDBVarDeclItem var = new SVDBVarDeclItem(type, name);
			
			ret.add(var);
			
			if (lexer().peekOperator("=")) {
				// TODO: eat tokens until ',' or ')'
			}
			
			// TODO: handle array, queue, etc
			if (lexer().peekOperator(",")) {
				lexer().eatToken();
			} else {
				break;
			}
		}
		
		lexer().readOperator(";");
		
		return ret;
	}

}
