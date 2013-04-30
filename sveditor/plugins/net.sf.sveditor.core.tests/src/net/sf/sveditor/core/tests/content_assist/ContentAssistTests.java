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
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.TextTagPosUtils;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class ContentAssistTests extends TestCase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("ContentAssistTests");
		suite.addTest(new TestSuite(TestArrayContentAssist.class));
		suite.addTest(new TestSuite(TestContentAssistBasics.class));
		suite.addTest(new TestSuite(TestContentAssistBehavioralBlock.class));
		suite.addTest(new TestSuite(TestContentAssistBuiltins.class));
		suite.addTest(new TestSuite(TestContentAssistClass.class));
		suite.addTest(new TestSuite(TestContentAssistEnum.class));
		suite.addTest(new TestSuite(TestContentAssistInterface.class));
		suite.addTest(new TestSuite(TestContentAssistModule.class));
		suite.addTest(new TestSuite(TestContentAssistPriority.class));
		suite.addTest(new TestSuite(TestContentAssistStruct.class));
		suite.addTest(new TestSuite(TestContentAssistSystem.class));
		suite.addTest(new TestSuite(TestContentAssistTaskFunction.class));
		suite.addTest(new TestSuite(TestContentAssistTypes.class));
		suite.addTest(new TestSuite(TestModuleContentAssist.class));
		suite.addTest(new TestSuite(TestParamClassContentAssist.class));
		
		return suite;
	}
	
	public static void validateResults(
			String 						expected[], 
			List<SVCompletionProposal>	proposals) {
		validateResults(expected, proposals, false);
	}

	public static void validateResults(
			String 						expected[], 
			List<SVCompletionProposal>	proposals,
			boolean						ordered) {
		for (int exp_idx=0; exp_idx<expected.length; exp_idx++) {
			String exp = expected[exp_idx];
			boolean found = false;
			
			if (ordered) {
				if (exp_idx < proposals.size()) {
					if (proposals.get(exp_idx).getReplacement().equals(exp)) {
						proposals.set(exp_idx, null);
						found = true;
					}
				}
			} else {
				for (int i=0; i<proposals.size(); i++) {
					if (proposals.get(i).getReplacement().equals(exp)) {
						found = true;
						proposals.remove(i);
						break;
					}
				}
			}
			
			assertTrue("Failed to find content proposal " + exp, found);
		}
		
		StringBuilder unexp = new StringBuilder("Unexpected proposals: ");
		int nonnull_proposals = 0;
		for (SVCompletionProposal p : proposals) {
			if (p != null) {
				nonnull_proposals++;
				unexp.append(p.getReplacement());
				unexp.append(" ");
			}
		}
		assertEquals(unexp.toString(), 0, nonnull_proposals);
	}
	
	public static void runTest(String testname, String doc, String ... expected) {
		LogHandle log = LogFactory.getLogHandle(testname);

		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(SVLanguageLevel.SystemVerilog, tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(expected, proposals, false);
		LogFactory.removeLogHandle(log);		
	}

	public static void runTestOrder(String testname, String doc, String ... expected) {
		LogHandle log = LogFactory.getLogHandle(testname);

		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(SVLanguageLevel.SystemVerilog, tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("   Proposal: " + p.getReplacement());
		}
		
		ContentAssistTests.validateResults(expected, proposals, true);
		LogFactory.removeLogHandle(log);		
	}
	
	public static void runTest(
			String 			testname, 
			String 			doc, 
			String			expected[],
			String			unexpected[]) {
		LogHandle log = LogFactory.getLogHandle(testname);

		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(SVLanguageLevel.SystemVerilog, tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(expected, proposals, false);
		LogFactory.removeLogHandle(log);		
	}	

	public static void runTest(
			String 					testname, 
			String 					doc, 
			ISVDBIndexIterator		index_it,
			String 		... 		expected) {
		LogHandle log = LogFactory.getLogHandle(testname);

		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(SVLanguageLevel.SystemVerilog, tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, index_it);
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(expected, proposals, false);
		LogFactory.removeLogHandle(log);		
	}
}
