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


package net.sf.sveditor.core.tests;

import junit.framework.Test;
import junit.framework.TestResult;
import junit.framework.TestSuite;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.tests.content_assist.ContentAssistTests;
import net.sf.sveditor.core.tests.indent.IndentTests;
import net.sf.sveditor.core.tests.index.IndexTests;
import net.sf.sveditor.core.tests.index.persistence.PersistenceTests;

public class ReleaseTests extends TestSuite {
	
	public ReleaseTests() {
		addTest(new TestSuite(SVScannerTests.class));
		addTest(IndentTests.suite());
		addTest(ContentAssistTests.suite());
		addTest(PersistenceTests.suite());
		addTest(IndexTests.suite());
	}
	
	@Override
	public void run(TestResult result) {
		SVCorePlugin.getDefault().enableDebug(false);
		// TODO Auto-generated method stub
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
		return new ReleaseTests();
	}
	
}
