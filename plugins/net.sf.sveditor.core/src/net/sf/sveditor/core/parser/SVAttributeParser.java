package net.sf.sveditor.core.parser;

import net.sf.sveditor.core.db.ISVDBAddChildItem;

public class SVAttributeParser extends SVParserBase {
	
	public SVAttributeParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(ISVDBAddChildItem parent) throws SVParseException {
		// TODO: save these later
		try {
			while (fLexer.peekOperator("(*")) {
				fLexer.setInAttr(true);
				fLexer.eatToken();

				while (fLexer.peek() != null) {
					fLexer.readId();

					if (fLexer.peekOperator("=")) {
						fLexer.eatToken();
						fParsers.exprParser().expression();
					}

					if (fLexer.peekOperator(",")) {
						fLexer.eatToken();
					} else {
						break;
					}
				}

				fLexer.readOperator("*)");
			}
		} finally {
			fLexer.setInAttr(false);
		}
	}

}
