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


package net.sf.sveditor.core.tests.content_assist;

import java.util.List;

import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class ContentAssistTests extends TestCase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("ContentAssistTests");
		suite.addTest(new TestSuite(TestContentAssistBasics.class));
		suite.addTest(new TestSuite(TestContentAssistStruct.class));
		suite.addTest(new TestSuite(TestContentAssistBuiltins.class));
		suite.addTest(new TestSuite(TestArrayContentAssist.class));
		suite.addTest(new TestSuite(TestParamClassContentAssist.class));
		
		return suite;
	}

	public static void validateResults(String expected[], List<SVCompletionProposal> proposals) {
		for (String exp : expected) {
			boolean found = false;
			for (int i=0; i<proposals.size(); i++) {
				if (proposals.get(i).getReplacement().equals(exp)) {
					found = true;
					proposals.remove(i);
					break;
				}
			}
			
			assertTrue("Failed to find content proposal " + exp, found);
		}
		
		for (SVCompletionProposal p : proposals) {
			System.out.println("[ERROR] Unexpected proposal " + p.getReplacement());
		}
		assertEquals("Unexpected proposals", 0, proposals.size());
	}
}
