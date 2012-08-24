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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.TextTagPosUtils;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class ContentAssistTests extends TestCase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("ContentAssistTests");
		suite.addTest(new TestSuite(TestContentAssistBasics.class));
		suite.addTest(new TestSuite(TestContentAssistEnum.class));
		suite.addTest(new TestSuite(TestContentAssistStruct.class));
		suite.addTest(new TestSuite(TestContentAssistBuiltins.class));
		suite.addTest(new TestSuite(TestArrayContentAssist.class));
		suite.addTest(new TestSuite(TestParamClassContentAssist.class));
		suite.addTest(new TestSuite(TestModuleContentAssist.class));
		suite.addTest(new TestSuite(TestContentAssistClass.class));
		suite.addTest(new TestSuite(TestContentAssistInterface.class));
		suite.addTest(new TestSuite(TestContentAssistBehavioralBlock.class));
		
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
	
	public static void runTest(String testname, String doc, String ... expected) {
		LogHandle log = LogFactory.getLogHandle(testname);

		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(expected, proposals);
		LogFactory.removeLogHandle(log);		
	}
}
