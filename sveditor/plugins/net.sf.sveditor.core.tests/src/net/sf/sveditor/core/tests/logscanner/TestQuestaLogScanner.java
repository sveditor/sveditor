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

import org.eclipse.hdt.sveditor.core.script.launch.LogMessageScannerMgr;
import org.eclipse.hdt.sveditor.core.script.launch.QuestaLogMessageScanner;
import org.eclipse.hdt.sveditor.core.script.launch.ScriptMessage;

import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestQuestaLogScanner extends SVCoreTestCaseBase {
	private LogMessageScannerMgr		fScannerMgr;
	
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fScannerMgr = new LogMessageScannerMgr("/home/test");
		fScannerMgr.addScanner(new QuestaLogMessageScanner());
	}
	
	public void testBasicError() {
		fScannerMgr.line("** Error: /home/test/foo/test.sv(1): compilation error");
		fScannerMgr.close();
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("compilation error", m.getMessage());
		assertEquals("/home/test/foo/test.sv", m.getPath());
		assertEquals(1, m.getLineno());
	}
	
	public void testErrorWithCode() {
		fScannerMgr.line("** Error: (vlog-1000) /home/test/foo/test.sv(1): compilation error");
		fScannerMgr.close();
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("compilation error", m.getMessage());
		assertEquals("/home/test/foo/test.sv", m.getPath());
		assertEquals(1, m.getLineno());
	}

	public void testSuppressibleError() {
		fScannerMgr.line("** Error (suppressible): (vlog-1100) /home/test/foo/test.sv(1): compilation error");
		fScannerMgr.close();
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("compilation error", m.getMessage());
		assertEquals("/home/test/foo/test.sv", m.getPath());
		assertEquals(1, m.getLineno());
	}

	public void testMultiLineError_1() {
		fScannerMgr.line("** Error: ** while parsing file included at ../foo.sv(10)");
		fScannerMgr.line("** at ../bar.sv(16): parse error");
		fScannerMgr.close();
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("parse error", m.getMessage());
		assertEquals("../bar.sv", m.getPath());
		assertEquals(16, m.getLineno());
	}
	
	public void testMultiLineError_2() {
		fScannerMgr.line("** Error: ** while parsing file included at ../foo.sv(10)");
		fScannerMgr.line("** while parsing macro expansion: foobar starting at  ../bar.sv(16): parse error");
		fScannerMgr.line("** at ../bar.sv(16): parse error");
		fScannerMgr.close();
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("parse error", m.getMessage());
		assertEquals("../bar.sv", m.getPath());
		assertEquals(16, m.getLineno());
	}	
	
	public void testMultiLineError_3() {
		fScannerMgr.line("** Error: ** while parsing file included at ../foo.sv(10)");
		fScannerMgr.line("** while parsing macro expansion: foobar starting at  ../bar.sv(16): parse error");
		fScannerMgr.line("** at ../bar.sv(16): (vlog-2730) parse error");
		fScannerMgr.close();
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("parse error", m.getMessage());
		assertEquals("../bar.sv", m.getPath());
		assertEquals(16, m.getLineno());
	}
}
