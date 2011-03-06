package net.sf.sveditor.core.parser;

import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.scanner.SVKeywords;

public class SVFieldVarDeclParser extends SVParserBase {
	
	public SVFieldVarDeclParser(ISVParser parser) {
		super(parser);
	}
	
	/**
	 * Checks to see if this is a declaration. Parses and returns if so. 
	 * 
	 * @param decl_allowed
	 * @return
	 */
	public ISVDBItemBase try_parse(boolean decl_allowed) throws SVParseException {
		if ((fLexer.peekKeyword(SVKeywords.fBuiltinTypes) && !fLexer.peekKeyword("void")) ||
				fLexer.isIdentifier() || fLexer.peekKeyword("typedef")) {
			boolean builtin_type = (fLexer.peekKeyword(SVKeywords.fBuiltinTypes) && !fLexer.peekKeyword("void"));
			
			if ((fLexer.peekKeyword(SVKeywords.fBuiltinTypes) && !fLexer.peekKeyword("void")) ||
					fLexer.peekKeyword("typedef")) {
				// Definitely a declaration
				if (!decl_allowed) {
					error("declaration in a post-declaration location");
				}
				SVDBStmt decl = parsers().blockItemDeclParser().parse();
				return decl;
			} else {
				// May be a declaration. Let's see
				
				// Variable declarations
				List<SVToken> id_list = parsers().SVParser().scopedStaticIdentifier_l(true);
			
				if (!builtin_type && (fLexer.peekOperator() && !fLexer.peekOperator("#"))) {
					// likely a statement
					for (int i=id_list.size()-1; i>=0; i--) {
						fLexer.ungetToken(id_list.get(i));
					}
					debug("non-declaration statement: " + fLexer.peek());
				} else {
					for (int i=id_list.size()-1; i>=0; i--) {
						fLexer.ungetToken(id_list.get(i));
					}
					debug("Pre-var parse: " + fLexer.peek());
					if (!decl_allowed) {
						error("declaration in a non-declaration location");
					}
					
					SVDBStmt decl = parsers().blockItemDeclParser().parse();
				
					// Bail for now
					return decl; 
				}
			}
		} else {
			
			// time to move on to the body
			debug("non-declaration statement: " + fLexer.peek());
		}
		
		return null;
	}

}
