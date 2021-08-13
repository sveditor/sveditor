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

import org.eclipse.hdt.sveditor.core.script.launch.LogMessageScannerMgr;
import org.eclipse.hdt.sveditor.core.script.launch.MakefileLogMessageScanner;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;

public class TestMakefileLogScanner extends SVCoreTestCaseBase {
	private LogMessageScannerMgr		fScannerMgr;
	
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fScannerMgr = new LogMessageScannerMgr("/home/test");
		fScannerMgr.addScanner(new MakefileLogMessageScanner());
	}
	
	public void testBasicDirectoryChange() {
		fScannerMgr.line("make: Entering directory '/scratch/other/foo'");
		fScannerMgr.close();
		
		assertEquals("/scratch/other/foo", fScannerMgr.getWorkingDirectory());
		
		fScannerMgr.line("make: Leaving directory '/scratch/other/foo'");
		
		assertEquals("/home/test", fScannerMgr.getWorkingDirectory());
		
		fScannerMgr.line("make: Leaving directory '/scratch/other/foo'");
		
		assertEquals("/home/test", fScannerMgr.getWorkingDirectory());
	}
	
	public void testBasicDirectoryChange2() {
		fScannerMgr.line("make[1]: Entering directory '/scratch/other/foo'");
		fScannerMgr.close();
		
		assertEquals("/scratch/other/foo", fScannerMgr.getWorkingDirectory());
		
		fScannerMgr.line("make[1]: Leaving directory '/scratch/other/foo'");
		
		assertEquals("/home/test", fScannerMgr.getWorkingDirectory());
		
		fScannerMgr.line("make[1]: Leaving directory '/scratch/other/foo'");
		
		assertEquals("/home/test", fScannerMgr.getWorkingDirectory());
	}	
}
