package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

public class SVCommonParserUtils extends SVParserBase {
	
	public SVCommonParserUtils(ISVParser parser) {
		super(parser);
	}

	/**
	 * Tries to read a scoped static identifier list
	 * 
	 * @param allow_keywords
	 * @return
	 * @throws SVParseException
	 */
	public List<SVToken> peekScopedStaticIdentifier_l(boolean allow_keywords) throws SVParseException {
		List<SVToken> ret = new ArrayList<SVToken>();

		if (!allow_keywords) {
			if (fLexer.peekId()) {
				ret.add(fLexer.readIdTok());
			} else {
				return ret;
			}
		} else if (fLexer.peekKeyword() || fLexer.peekId()) {
			ret.add(fLexer.consumeToken());
		} else {
			return ret;
		}

		while (fLexer.peekOperator("::")) {
			ret.add(fLexer.consumeToken());
			if (allow_keywords && fLexer.peekKeyword()) {
				ret.add(fLexer.consumeToken());
			} else {
				ret.add(fLexer.readIdTok());
			}
		}

		return ret;
	}
}
