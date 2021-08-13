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
package org.eclipse.hdt.sveditor.core.tests.argfile.parser;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileExprContext;
import org.eclipse.hdt.sveditor.core.argfile.parser.SVArgFileExprScanner;
import org.eclipse.hdt.sveditor.core.scanutils.StringBIDITextScanner;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.TextTagPosUtils;

public class TestArgFileExprScanner extends SVCoreTestCaseBase {

	public void testFilePathContentAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"${workspace_loc}/foo.sv\n" +
			"+incdir+${workspace_loc}/path1/path2/a<<MARK>>\n"
			;
	
		runTest(doc, "+incdir+", "${workspace_loc}/path1/path2/a");
	}

	public void testFileOptionContentAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"${workspace_loc}/foo.sv\n" +
			"-I <<MARK>>\n"
			;
		
		runTest(doc, "-I", null);
	}

	public void testIncdirPathContentAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"${workspace_loc}/foo.sv\n" +
			"+incdir+/tools/include/<<MARK>>\n"
			;
		
		runTest(doc, "+incdir+", "/tools/include/");
	}
	
	public void testPlusargOptionAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"+inc<<MARK>>\n";
			;
		
		runTest(doc, null, "+inc");
	}
	
	public void testOptionAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"-I<<MARK>>\n";
			;
		
		runTest(doc, null, "-I");
	}

	public void testEmptyAssist_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"<<MARK>>\n";
			;
		
		runTest(doc, null, "");
	}
	
	public void testEmptyAssist_2() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"/foo/bar <<MARK>>\n";
			;
		
		runTest(doc, null, "");
	}
	
	private void runTest(
			String				doc,
			String				exp_root,
			String				exp_leaf) {
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		fLog.debug("MARK offset=" + tt_utils.getPosMap().get("MARK") + 
				" doc.length=" + doc.length());
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));
		SVArgFileExprScanner expr_scanner = new SVArgFileExprScanner();
		
		SVArgFileExprContext ctxt = expr_scanner.extractExprContext(scanner, false);
		
		assertEquals("Expected root", exp_root, ctxt.fRoot);
		assertEquals("Expected leaf", exp_leaf, ctxt.fLeaf);
	}
}
