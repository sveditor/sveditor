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
package org.eclipse.hdt.sveditor.core.tests.logscanner;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.script.launch.LogMessageScannerMgr;
import org.eclipse.hdt.sveditor.core.script.launch.NCSimLogMessageScanner;
import org.eclipse.hdt.sveditor.core.script.launch.ScriptMessage;
import org.eclipse.hdt.sveditor.core.script.launch.ScriptMessage.MessageType;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;

public class TestNCSimLogScanner extends SVCoreTestCaseBase {
	private LogMessageScannerMgr		fScannerMgr;
	
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fScannerMgr = new LogMessageScannerMgr("/home/test");
		fScannerMgr.addScanner(new NCSimLogMessageScanner());
	}
	
	public void testBasicError() {
		SVCorePlugin.getDefault().enableDebug(false);
		fScannerMgr.line("                  foo.a = ENUM_VALUE_1;");
		fScannerMgr.line("                          |");
		fScannerMgr.line("ncvlog: *E,UNDIDN (/home/username/projects/project_name/trunk/driver.sv,358|58): 'ENUM_VALUE_1': undeclared identifier [12.5(IEEE)].");
		fScannerMgr.close();
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("'ENUM_VALUE_1': undeclared identifier [12.5(IEEE)].", m.getMessage());
		assertEquals("/home/username/projects/project_name/trunk/driver.sv", m.getPath());
		assertEquals(MessageType.Error, m.getType());
		assertEquals(358, m.getLineno());
	}
	
	public void testBasicWarning() {
		fScannerMgr.line("               foo.do();");
		fScannerMgr.line("                   |");
		fScannerMgr.line("ncvlog: *W,FUNTSK (/home/username/projects/project_name/trunk/driver.sv,306|38): function called as a task without void'().");
		
		assertEquals(1, fScannerMgr.getMessages().size());
		ScriptMessage m = fScannerMgr.getMessages().get(0);
		
		assertEquals("function called as a task without void'().", m.getMessage());
		assertEquals("/home/username/projects/project_name/trunk/driver.sv", m.getPath());
		assertEquals(MessageType.Warning, m.getType());
		assertEquals(306, m.getLineno());
	}
	
}
