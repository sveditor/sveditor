/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.parser;

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

		while (fLexer.peekOperator(OP.COLON2)) {
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
