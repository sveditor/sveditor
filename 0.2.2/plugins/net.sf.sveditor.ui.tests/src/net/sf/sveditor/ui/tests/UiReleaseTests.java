/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.tests;

import junit.framework.Test;
import junit.framework.TestResult;
import junit.framework.TestSuite;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.ui.tests.editor.TestAutoIndent;

public class UiReleaseTests extends TestSuite {
	
	public UiReleaseTests() {
		addTest(new TestSuite(TestAutoIndent.class));
	}
	
	@Override
	public void run(TestResult result) {
		SVCorePlugin.getDefault().enableDebug(false);
		super.run(result);
	}



	@Override
	public void runTest(Test test, TestResult result) {
		SVCorePlugin.getDefault().enableDebug(false);
		super.runTest(test, result);
	}



	public static Test suite() {
		
		/*
		TestSuite suite = new TestSuite();
		suite.addTest(new TestSuite(SVScannerTests.class));
		suite.addTest(IndentTests.suite());
		suite.addTest(ContentAssistTests.suite());
		suite.addTest(PersistenceTests.suite());
		suite.addTest(IndexTests.suite());
		
		return suite;
		 */
		return new UiReleaseTests();
	}
	
}
