package net.sf.sveditor.core.parser;

import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVTaskFuncBodyParser extends SVParserBase {
	
	public SVTaskFuncBodyParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(SVDBTaskFuncScope tf, boolean is_ansi) throws SVParseException {
		String decl_keywords[];
		String decl_keywords_ansi[] = {"const", "var", "automatic", "static", "typedef"};
		String decl_keywords_nonansi[] = {"const", "var", "automatic", "static", "typedef", "input", "output", "inout", "ref"};
		String end_keyword = (tf.getType() == SVDBItemType.Function)?"endfunction":"endtask";
		
		decl_keywords = (is_ansi)?decl_keywords_ansi:decl_keywords_nonansi;
		
		// parse declarations first. If non-ansi, port declarations are okay too
		String id = null;
		while (true) {
			id = null;
			System.out.println("token: " + lexer().peek());
			if (lexer().peekKeyword(decl_keywords) || 
					SVKeywords.isBuiltInType(lexer().peek()) ||
					lexer().isIdentifier()) {
				// Variable declarations
				id = lexer().eatToken(); // should be beginning of type declaration
				
				if ((lexer().peekKeyword() && !lexer().peekKeyword(decl_keywords_nonansi)) ||
						(lexer().peekOperator() && !lexer().peekOperator("#"))) {
					// likely a statement
					System.out.println("leaving decl section");
					break;
				}
				
				System.out.println("calling blockItemDeclParser with: \"" + id + "\"");
				List<SVDBItem> vars = parsers().blockItemDeclParser().parse(id);
				for (SVDBItem it : vars) {
					System.out.println("Add var: " + it.getName());
				}
				tf.addItems(vars);
			} else if (lexer().peekKeyword("typedef")) {
				// TODO: permit local type declaration
				break;
			} else {
				// time to move on to the body
				break;
			}
		}

		// now the task/function function body
		// this is much
		while (true) {
			if (lexer().peekKeyword(end_keyword)) {
				break;
			} else if (ParserSVDBFileFactory.isFirstLevelScope(lexer().peek(), 0)) {
				lexer().parseException("Missing function end");
			} else {
				id = lexer().eatToken();
			}
		}
	}

}
