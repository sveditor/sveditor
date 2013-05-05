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
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVDBIndexValidator;
import net.sf.sveditor.core.tests.TextTagPosUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestArrayContentAssist extends SVCoreTestCaseBase {
	private static ContentAssistIndex			fIndex;
	private static SVDBIndexCollection			fIndexMgr;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fIndex = new ContentAssistIndex();
		fIndex.init(new NullProgressMonitor());
		fIndexMgr = new SVDBIndexCollection("GLOBAL");
		fIndexMgr.addLibraryPath(fIndex);
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				SVDBIndexRegistry.GLOBAL_PROJECT, 
				SVCorePlugin.SV_BUILTIN_LIBRARY, 
				SVDBPluginLibIndexFactory.TYPE, null);
		fIndexMgr.addPluginLibrary(index);		
	}
	
	public void testMultiple() {
		LogHandle log = LogFactory.getLogHandle("testQueueFunctions");
		String doc_arr[] = {
			// Document 0
			"class elem_t;\n" +
			"    int my_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_t			m_queue_item[$];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item.<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n",
			// Document 1
			"class elem_c;\n" +
			"    int     m_int_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_c		m_queue_item[$];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item[0].<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n",
			// Document 2
			"class elem_t;\n" +
			"    int my_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_t			m_queue_item[];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item.<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n",
			// Document 3
			"class elem_c;\n" +
			"    int     m_int_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_c		m_queue_item[];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item[0].<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
		};
		
		String [] exp_arr[] = {
				new String[] { "size", "insert", "delete", "pop_front",
						"pop_back", "push_front", "push_back"},
				new String[] {"m_int_field"},
				new String[] {"size"},
				new String[] {"m_int_field"}				
		};

		SVCorePlugin.getDefault().enableDebug(false);
		for (int i=0; i<doc_arr.length; i++) {
			Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc_arr[i]);

			StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
			TestCompletionProcessor cp = new TestCompletionProcessor(log, ini.first(), fIndexMgr);

			scanner.seek(ini.second().getPosMap().get("MARK"));

			ISVDBIndexIterator index_it = cp.getIndexIterator();
			SVDBIndexValidator v = new SVDBIndexValidator();

			v.validateIndex(index_it, SVDBIndexValidator.ExpectErrors);

			IndexTestUtils.assertFileHasElements(index_it, "my_class1");

			cp.computeProposals(scanner, ini.first(), 
					ini.second().getLineMap().get("MARK"));
			List<SVCompletionProposal> proposals = cp.getCompletionProposals();

			validateResults(exp_arr[i], proposals);
		}
		
		LogFactory.removeLogHandle(log);
	}

	public void testQueueFunctions() {
		LogHandle log = LogFactory.getLogHandle("testQueueFunctions");
		String doc =
			"class elem_t;\n" +
			"    int my_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_t			m_queue_item[$];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item.<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(log, ini.first(), fIndexMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		ISVDBIndexIterator index_it = cp.getIndexIterator();
		SVDBIndexValidator v = new SVDBIndexValidator();
		
		v.validateIndex(index_it, SVDBIndexValidator.ExpectErrors);
		
		IndexTestUtils.assertFileHasElements(index_it, "my_class1");
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {
				"size", "insert", "delete", "pop_front",
				"pop_back", "push_front", "push_back"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testQueueElemItems() {
		LogHandle log = LogFactory.getLogHandle("testQueueElemItems");
		String doc =
			"class elem_c;\n" +
			"    int     m_int_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_c		m_queue_item[$];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item[0].<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(log, ini.first(), fIndexMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		ISVDBIndexIterator index_it = cp.getIndexIterator();
		SVDBIndexValidator v = new SVDBIndexValidator();
		
		v.validateIndex(index_it, SVDBIndexValidator.ExpectErrors);
	
		IndexTestUtils.assertFileHasElements(index_it, "my_class1");
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"m_int_field"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testArrayFunctions() {
		LogHandle log = LogFactory.getLogHandle("testArrayFunctions");
		String doc =
			"class elem_t;\n" +
			"    int my_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_t			m_queue_item[];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item.<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);

		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(log, ini.first(), fIndexMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		ISVDBIndexIterator index_it = cp.getIndexIterator();
		SVDBIndexValidator v = new SVDBIndexValidator();
		
		v.validateIndex(index_it, SVDBIndexValidator.ExpectErrors);
		
		IndexTestUtils.assertFileHasElements(index_it, "my_class1");
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		// TODO: at some point, my_class1 and my_class2 will not be proposals,
		// since they are types not variables 
		validateResults(new String[] {"size"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testArrayElemItems() {
		LogHandle log = LogFactory.getLogHandle("testArrayElemItems");
		String doc =
			"class elem_c;\n" +
			"    int     m_int_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_c		m_queue_item[];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item[0].<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(log, ini.first(), fIndexMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		ISVDBIndexIterator index_it = cp.getIndexIterator();
		SVDBIndexValidator v = new SVDBIndexValidator();
		
		v.validateIndex(index_it, SVDBIndexValidator.ExpectErrors);
		
		IndexTestUtils.assertFileHasElements(index_it, "my_class1");
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"m_int_field"}, proposals);
		LogFactory.removeLogHandle(log);
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
