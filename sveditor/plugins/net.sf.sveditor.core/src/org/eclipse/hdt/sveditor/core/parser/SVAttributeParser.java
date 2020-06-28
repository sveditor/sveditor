/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.parser;

import org.eclipse.hdt.sveditor.core.db.ISVDBAddChildItem;

public class SVAttributeParser extends SVParserBase {
	
	public SVAttributeParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(ISVDBAddChildItem parent) throws SVParseException {
		// TODO: save these later
		try {
			while (fLexer.peekOperator(OP.LPAREN_MUL)) {
				fLexer.setInAttr(true);
				fLexer.eatToken();

				while (fLexer.peek() != null) {
					fLexer.readId();

					if (fLexer.peekOperator(OP.EQ)) {
						fLexer.eatToken();
						fParsers.exprParser().expression();
					}

					if (fLexer.peekOperator(OP.COMMA)) {
						fLexer.eatToken();
					} else {
						break;
					}
				}

				fLexer.readOperator(OP.MUL_RPAREN);
			}
		} finally {
			fLexer.setInAttr(false);
		}
	}

}
