/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.content_assist;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBMacroDef;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBFileOverrideIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.parser.SVParser;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor;
import net.sf.sveditor.core.preproc.SVStringPreProcessor;
import net.sf.sveditor.core.scanner.SVKeywords;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.TextTagPosUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

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
			
//			System.out.println("[" + exp_idx + "] exp=\"" + exp + "\"");
			
			if (ordered) {
				if (exp_idx < proposals.size()) {
//					System.out.println("[" + exp_idx + "] proposal=\"" + proposals.get(exp_idx).getReplacement() + "\"");
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
	
	public static void runTest(
			SVCoreTestCaseBase		test,
			String 					doc, 
			String ... 				expected) {
		runTest(test, null, doc, false, expected);
	}
	
	public static void runTest(
			SVCoreTestCaseBase		test,
			String 					doc, 
			boolean					exclude_kw,
			String  				expected[]) {
		runTest(test, null, doc, exclude_kw, expected);
	}
	
	public static void runTest(
			SVCoreTestCaseBase			test,
			ISVDBIndex					extra_index,
			String						doc,
			String ...					expected) {
		runTest(test, extra_index, doc, false, expected);
	}
	
	public static void runTest(
			SVCoreTestCaseBase			test,
			ISVDBIndex					extra_index,
			String						doc,
			boolean						exclude_kw,
			String ...					expected) {
		LogHandle log = test.getLog();
		File tmpdir = test.getTmpDir();
		String testname = test.getName();
		
		File index_dir = new File(tmpdir, "__index_dir");
		TestCase.assertTrue(index_dir.mkdirs());
		
		TestUtils.copy(doc, 
				new File(index_dir, "doc.sv"));
		TestUtils.copy(
				new File(index_dir, "doc.sv").getAbsolutePath(), 
				new File(index_dir, "doc.f"));
		
		ISVDBIndex index = null; // TODO: create index

		try {
			TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));

			List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
			SVParser factory = new SVParser();
			SVPreProcessor preproc = new SVPreProcessor(testname, tt_utils.openStream(), null, null);

			SVPreProcOutput out = preproc.preprocess();

			SVDBFile file = factory.parse(SVLanguageLevel.SystemVerilog, out, testname, markers);
			StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());

			for (ISVDBItemBase it : file.getChildren()) {
				log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
			}
			
			index = test.getIndexRgy().findCreateIndex(
					new NullProgressMonitor(),
					testname,
					new File(index_dir, "doc.f").getAbsolutePath(),
					SVDBArgFileIndexFactory.TYPE,
					null);

			SVDBIndexCollection index_c = new SVDBIndexCollection(testname);
			index_c.addArgFilePath(index);
			if (extra_index != null) {
				index_c.addArgFilePath(extra_index);
			}
			index_c.addPluginLibrary(SVCorePlugin.getDefault().getBuiltinLib());
			
			for (ISVDBIndex i : index_c.getIndexList()) {
				i.execIndexChangePlan(new NullProgressMonitor(), 
						new SVDBIndexChangePlanRebuild(i));
			}

			Tuple<SVDBFile, SVDBFile> new_in = index.parse(
					new NullProgressMonitor(),
					new StringInputStream(doc),
					new File(index_dir, "doc.sv").getAbsolutePath(),
					markers);

			SVDBFileOverrideIndex cp_index = new SVDBFileOverrideIndex(
					new_in.second(),    // Parse tree from the 'live' version
					new_in.first(), // PreProc tree 
					index,   // Specific index we're working with
					index_c, // Index collection we're working with
					markers);

			TestCompletionProcessor cp = new TestCompletionProcessor(
					log, file, cp_index);

			List<SVDBMacroDef> macros = new ArrayList<SVDBMacroDef>();

			for (SVDBMacroDef m : preproc.getDefaultMacros()) {
				macros.add(m);
			}

			ISVStringPreProcessor pp = new SVStringPreProcessor(macros);

			cp.setPreProcessor(pp); // ??

			scanner.seek(tt_utils.getPosMap().get("MARK"));

			cp.computeProposals(
					scanner, 
					file, 
					tt_utils.getLineMap().get("MARK"));
			List<SVCompletionProposal> proposals = cp.getCompletionProposals();
			
			if (exclude_kw) {
				for (int i=0; i<proposals.size(); i++) {
					if (SVKeywords.isSVKeyword(proposals.get(i).getReplacement())) {
						proposals.remove(i);
						i--;
					}
				}				
			}

			ContentAssistTests.validateResults(expected, proposals, false);
		} finally {
			test.getIndexRgy().disposeIndex(index, "End of Test");
			if (extra_index != null) {
				test.getIndexRgy().disposeIndex(extra_index, "End of Test");
			}
			TestUtils.delete(index_dir);
		}		
	}
	
	public static void runTestOrder(
			String testname, 
			ISVDBIndexCacheMgr		cache_mgr,
			String doc, 
			String ... expected) {
		LogHandle log = LogFactory.getLogHandle(testname);

		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory();
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(SVLanguageLevel.SystemVerilog, tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		ISVDBIndexCache cache = FileIndexIterator.createCache(cache_mgr);
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file, cache));
		
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
			ISVDBIndexCacheMgr		cache_mgr,
			String 			doc, 
			String			expected[],
			String			unexpected[]) {
		LogHandle log = LogFactory.getLogHandle(testname);

		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory();
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(SVLanguageLevel.SystemVerilog, tt_utils.openStream(), testname, markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		ISVDBIndexCache cache = FileIndexIterator.createCache(cache_mgr);
		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file, cache));
		
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
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory();
		
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
