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
package org.eclipse.hdt.sveditor.core.tests.content_assist;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.expr_utils.SVExprContext;
import org.eclipse.hdt.sveditor.core.expr_utils.SVExprScanner;
import org.eclipse.hdt.sveditor.core.scanutils.IBIDITextScanner;
import org.eclipse.hdt.sveditor.core.scanutils.StringBIDITextScanner;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;

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
