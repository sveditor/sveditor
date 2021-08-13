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
package org.sveditor.core.tests.content_assist;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.expr_utils.SVExprContext;
import org.sveditor.core.expr_utils.SVExprScanner;
import org.sveditor.core.scanutils.IBIDITextScanner;
import org.sveditor.core.scanutils.StringBIDITextScanner;

import org.sveditor.core.tests.SVCoreTestCaseBase;

public class TestExprScanner extends SVCoreTestCaseBase {
	
	public void testIncludeFindsQuotes() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
				"`include \"\n"
				;

		StringBIDITextScanner ss = new StringBIDITextScanner(doc);
		ss.seek(doc.length()-1);
		
		SVExprScanner scanner = new SVExprScanner();
		SVExprContext ctxt = scanner.extractExprContext(ss, false);
		
		System.out.println("ctxt: " + ctxt.fRoot + " " + ctxt.fLeaf + " ");
	}

}
