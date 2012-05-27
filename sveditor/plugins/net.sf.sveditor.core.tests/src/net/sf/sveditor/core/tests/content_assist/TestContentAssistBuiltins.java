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

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBCovergroup;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.SVDBIndexValidator;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.TextTagPosUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestContentAssistBuiltins extends TestCase {
	private ContentAssistIndex			fIndex;
	private SVDBIndexCollection		fIndexMgr;
	private File						fTmpDir;
	
	@Override
	public void setUp() {
		fTmpDir = TestUtils.createTempDir();
		
		fIndexMgr = new SVDBIndexCollection("TestContentAssistBuiltins");
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(fTmpDir));
		fIndexMgr.addPluginLibrary(
				rgy.findCreateIndex(new NullProgressMonitor(),
						"TestContentAssistBuiltins", SVCorePlugin.SV_BUILTIN_LIBRARY, 
						SVDBPluginLibIndexFactory.TYPE, null));

		fIndex = new ContentAssistIndex();
		fIndex.init(new NullProgressMonitor());
		fIndexMgr.addLibraryPath(fIndex);
	}
	
	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		TestUtils.delete(fTmpDir);
	}

	public void testCovergroupOption() {
		LogHandle log = LogFactory.getLogHandle("testCovergroupOption");
		String doc =
			"class my_class1;\n" +							// 1
			"\n" +											// 2
			"    covergroup foo;\n" +						// 3
			"        option.per_<<MARK>>\n" +				// 4
			"    endgroup\n" +
			"endclass\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndexMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		ISVDBIndexIterator index_it = cp.getIndexIterator();
		ISVDBItemIterator it = index_it.getItemIterator(new NullProgressMonitor());
		SVDBIndexValidator v = new SVDBIndexValidator();
		
		v.validateIndex(index_it.getItemIterator(new NullProgressMonitor()), SVDBIndexValidator.ExpectErrors);
		
		SVDBCovergroup cg = null;
		SVDBClassDecl my_class1 = null;
		it = index_it.getItemIterator(new NullProgressMonitor());
		
		while (it.hasNext()) {
			ISVDBItemBase it_t = it.nextItem();
			
			if (it_t.getType() == SVDBItemType.Covergroup && 
					SVDBItem.getName(it_t).equals("foo")) {
				cg = (SVDBCovergroup)it_t;
			} else if (it_t.getType() == SVDBItemType.ClassDecl &&
					SVDBItem.getName(it_t).equals("my_class1")) {
				my_class1 = (SVDBClassDecl)it_t;
			}
		}
		
		assertNotNull(cg);
		assertNotNull(my_class1);
		
		log.debug("");
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		// TODO: at some point, my_class1 and my_class2 will not be proposals,
		// since they are types not variables 
		validateResults(new String[] {"per_instance"}, proposals);
		
		LogFactory.removeLogHandle(log);
	}

	public void testCovergroupTypeOptionMergeInstances() {
		String doc =
			"class my_class1;\n" +							// 1
			"\n" +
			"    covergroup foo;\n" +
			"        type_option.mer<<MARK>>\n" +
			"    endgroup\n" +
			"endclass\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndexMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		ISVDBIndexIterator index_it = cp.getIndexIterator();
		ISVDBItemIterator it = index_it.getItemIterator(new NullProgressMonitor());
		SVDBIndexValidator v = new SVDBIndexValidator();
		
		v.validateIndex(index_it.getItemIterator(new NullProgressMonitor()), SVDBIndexValidator.ExpectErrors);
		
		SVDBCovergroup cg = null;
		SVDBClassDecl my_class1 = null;
		it = index_it.getItemIterator(new NullProgressMonitor());
		
		while (it.hasNext()) {
			ISVDBItemBase it_t = it.nextItem();
			
			if (it_t.getType() == SVDBItemType.Covergroup && 
					SVDBItem.getName(it_t).equals("foo")) {
				cg = (SVDBCovergroup)it_t;
			} else if (it_t.getType() == SVDBItemType.ClassDecl &&
					SVDBItem.getName(it_t).equals("my_class1")) {
				my_class1 = (SVDBClassDecl)it_t;
			}
		}
		
		assertNotNull(cg);
		assertNotNull(my_class1);
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		assertEquals(1, proposals.size());
		
		// TODO: at some point, my_class1 and my_class2 will not be proposals,
		// since they are types not variables 
		validateResults(new String[] {"merge_instances"}, proposals);
	}

	/*************** Utility Methods ********************/
	private Tuple<SVDBFile, TextTagPosUtils> contentAssistSetup(String doc) {
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc", markers);
		fIndex.setFile(file);

		return new Tuple<SVDBFile, TextTagPosUtils>(file, tt_utils);
	}
	
	private void validateResults(String expected[], List<SVCompletionProposal> proposals) {
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
