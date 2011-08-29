/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


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
