package net.sf.sveditor.core.parser;

import java.util.List;

import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;

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
		while (true) {
			if (lexer().peekKeyword(decl_keywords) || !lexer().isKeyword()) {
				// Variable declarations
				
				List<SVDBItem> vars = parsers().blockItemDeclParser().parse();
				for (SVDBItem var : vars) {
					tf.addItem(var);
				}
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
				throw new SVParseException("Missing function end");
			} else {
				lexer().eatToken();
			}
		}
	}

}
