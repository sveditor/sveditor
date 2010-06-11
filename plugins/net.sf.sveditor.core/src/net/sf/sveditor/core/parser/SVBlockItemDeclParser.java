package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVBlockItemDeclParser extends SVParserBase {
	
	public SVBlockItemDeclParser(ISVParser parser) {
		super(parser);
	}
	
	public List<SVDBItem> parse(String id) throws SVParseException {
		List<SVDBItem> ret = new ArrayList<SVDBItem>();
		
		if (id.equals("const")) {
			id = lexer().eatToken();
		}
		if (id.equals("var")) {
			id = lexer().eatToken();
		}

		if (id.equals("static") || id.equals("automatic")) {
			id = lexer().eatToken();
		}
		
		// Should be the data-type
		// String id = lexer().eatToken();
		if ((SVKeywords.isBuiltInType(id) && !id.equals("void")) || 
				!SVKeywords.isSVKeyword(id)) {
			// Data declaration or statement
			SVDBTypeInfo type = parsers().dataTypeParser().data_type(id);
			
			while (true) {
				String name = lexer().readId();
			
				SVDBVarDeclItem var = new SVDBVarDeclItem(type, name, 0);
			
				ret.add(var);

				// TODO: handle array, queue, etc
				if (lexer().peekOperator("[")) {
					lexer().eatToken();
					
					// array or queue
					if (lexer().peekOperator("$")) {
						// queue
						lexer().eatToken();
						lexer().readOperator("]");
					} else if (lexer().peekOperator("]")) {
						lexer().readOperator("]");
					} else {
						// bounded array
						lexer().skipPastMatch("[", "]");
					}
				}

				if (lexer().peekOperator("=")) {
					// TODO: eat tokens until ',' or ';'
					lexer().eatToken();
					parsers().SVParser().readExpression();
					/*
					while(lexer().peek() != null && !lexer().peekOperator(",", ";")) {
						lexer().eatToken();
					}
					 */
				}
			
				if (lexer().peekOperator(",")) {
					lexer().eatToken();
				} else {
					break;
				}
			}
		} else {
			lexer().parseException("Unexpected ");
		}
		
		
		lexer().readOperator(";");
		
		return ret;
	}
}
