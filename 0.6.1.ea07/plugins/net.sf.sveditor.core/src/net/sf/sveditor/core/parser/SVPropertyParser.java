package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.ISVDBAddChildItem;
import net.sf.sveditor.core.db.SVDBProperty;

public class SVPropertyParser extends SVParserBase {
	
	public SVPropertyParser(ISVParser parser) {
		super(parser);
	}
	
	public void property(ISVDBAddChildItem parent) throws SVParseException {
		SVDBProperty prop = new SVDBProperty();
		fLexer.readKeyword("property");

		prop.setName(fLexer.readId());
		
		if (fLexer.peekOperator("(")) {
			// TODO: argument list
		}
		fLexer.readOperator(";");
		
		parent.addChildItem(prop);
		
		try {
			
		} finally {
			prop.setEndLocation(fLexer.getStartLocation());
		}

		fLexer.readKeyword("endproperty");
		
		if (fLexer.peekOperator(":")) {
			fLexer.eatToken();
			fLexer.readId();
		}
	}

}
