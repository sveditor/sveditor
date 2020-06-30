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
package net.sf.sveditor.core.tests.logscanner;

import org.eclipse.hdt.sveditor.core.script.launch.GccLogMessageScanner;
import org.eclipse.hdt.sveditor.core.script.launch.LogMessageScannerMgr;
import org.eclipse.hdt.sveditor.core.script.launch.MakefileLogMessageScanner;
import org.eclipse.hdt.sveditor.core.script.launch.ScriptMessage;

import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestGccLogScanner extends SVCoreTestCaseBase {
	private LogMessageScannerMgr		fScannerMgr;
	
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fScannerMgr = new LogMessageScannerMgr("/home/test");
		fScannerMgr.addScanner(new GccLogMessageScanner());
	}
	
	public void testBasics() {
		fScannerMgr.line("/home/test/foo/test.cpp:1:10: error: compilation error");
		fScannerMgr.close();
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("compilation error", m.getMessage());
		assertEquals("/home/test/foo/test.cpp", m.getPath());
		assertEquals(1, m.getLineno());
	}
}
