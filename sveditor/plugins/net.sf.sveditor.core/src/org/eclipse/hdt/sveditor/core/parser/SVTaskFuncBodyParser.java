/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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

import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBTask;

public class SVTaskFuncBodyParser extends SVParserBase {
	
	public SVTaskFuncBodyParser(ISVParser parser) {
		super(parser);
	}
	
	public void parse(SVDBTask tf, boolean is_ansi) throws SVParseException {
		KW end_keyword = (tf.getType() == SVDBItemType.Function)?KW.ENDFUNCTION:KW.ENDTASK;
		if (fDebugEn) {
			debug("--> SVTaskFuncBodyParser: " + fLexer.peek());
			debug("SVTaskFuncBodyParse: is_ansi=" + is_ansi);
		}
		
		
		// Parse the task/function body, including declarations
		// decl_allowed tracks the 
		boolean decl_allowed = true;
		while (fLexer.peek() != null) {
			if (fLexer.peekKeyword(end_keyword)) {
				break;
			// check for parameters - these can be used in port lists etc.
			} else if (fLexer.peekKeyword(KW.PARAMETER) || fLexer.peekKeyword(KW.LOCALPARAM)) {
				parsers().modIfcBodyItemParser().parse_parameter_decl(tf);
			} else if (SVParser.isFirstLevelScope(fLexer.peek(), 0)) {
				error("Missing " + ((tf.getType() == SVDBItemType.Function)?"function":"task") + " end");
			} else {
				decl_allowed = parsers().behavioralBlockParser().statement(tf, decl_allowed, is_ansi);
			}
		}
		
		if (fDebugEn) {
			debug("<-- SVTaskFuncBodyParser: " + fLexer.peek());
		}
	}
}
