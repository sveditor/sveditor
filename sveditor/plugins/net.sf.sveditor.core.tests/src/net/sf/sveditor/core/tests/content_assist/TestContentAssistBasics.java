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
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBTask;
import net.sf.sveditor.core.db.SVDBUtil;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanner.SVKeywords;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBIndexValidator;
import net.sf.sveditor.core.tests.TestNullIndexCacheFactory;
import net.sf.sveditor.core.tests.TextTagPosUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestContentAssistBasics extends TestCase {
	private SVDBIndexCollection		fIndexCollectionOVMMgr;
	private SVDBIndexCollection		fIndexCollectionVMMMgr;
	private SVDBIndexCollection		fIndexCollectionStandalone;
	private ContentAssistIndex			fIndex;
	private File						fTmpDir;
	
	@Override
	public void setUp() {
		fTmpDir = TestUtils.createTempDir();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		utils.copyBundleDirToFS("/data/basic_content_assist_project", fTmpDir);

		String pname = "basic_content_assist_project";
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(new TestNullIndexCacheFactory());
		fIndex = new ContentAssistIndex();
		fIndex.init(new NullProgressMonitor());

		fIndexCollectionVMMMgr = new SVDBIndexCollection(pname);
		fIndexCollectionVMMMgr.addLibraryPath(fIndex);
		fIndexCollectionVMMMgr.addPluginLibrary(
				rgy.findCreateIndex(new NullProgressMonitor(), pname, 
						SVCoreTestsPlugin.VMM_LIBRARY_ID, 
						SVDBPluginLibIndexFactory.TYPE, null));
	}
	
	private SVDBIndexCollection createStandaloneIndexMgr() {
		if (fIndexCollectionStandalone == null) {
			fIndexCollectionStandalone = new SVDBIndexCollection("GLOBAL");
			fIndexCollectionStandalone.addLibraryPath(fIndex);
		}
		return fIndexCollectionStandalone;
	}

	private SVDBIndexCollection createOVMIndexMgr() {
		if (fIndexCollectionOVMMgr == null) {
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			fIndexCollectionOVMMgr = new SVDBIndexCollection("GLOBAL");
			fIndexCollectionOVMMgr.addLibraryPath(fIndex);
			fIndexCollectionOVMMgr.addPluginLibrary(
					rgy.findCreateIndex(new NullProgressMonitor(), "GLOBAL", 
							SVCoreTestsPlugin.OVM_LIBRARY_ID, 
							SVDBPluginLibIndexFactory.TYPE, null));
			fIndexCollectionOVMMgr.loadIndex(new NullProgressMonitor());
		}
		return fIndexCollectionOVMMgr;
	}
	
	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		TestUtils.delete(fTmpDir);
	}
	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testOVMMacroContentAssist() {
//		SVCorePlugin.getDefault().enableDebug(false);
		String testname = "testOVMMacroContentAssist";
		SVCorePlugin.getDefault().setDebugLevel(ILogLevel.LEVEL_OFF);
		LogHandle log = LogFactory.getLogHandle(testname);
		
		String doc1 = 
			"class my_class;\n" +
			"    `ovm_componen<<FIELD1>>\n" +
			"endclass\n";
		
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc1);
		TextTagPosUtils tt_utils = ini.second();
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1", markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());

		TestCompletionProcessor cp = new TestCompletionProcessor(
				testname, file, createOVMIndexMgr());
		
		scanner.seek(tt_utils.getPosMap().get("FIELD1"));

		log.debug(ILogLevel.LEVEL_MIN, "--> computeProposals");
		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("FIELD1"));
		log.debug(ILogLevel.LEVEL_MIN, "<-- computeProposals");
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"ovm_component_utils", "ovm_component_param_utils", 
				"ovm_component_utils_begin", "ovm_component_param_utils_begin", 
				"ovm_component_utils_end", "ovm_component_new_func", 
				"ovm_component_factory_create_func", "ovm_component_registry",
				"ovm_component_registry_internal", "ovm_component_registry_param",
				"OVM_COMPONENT_SVH"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testVMMMacroContentAssist() {
		String doc1 = 
			"class my_class;\n" +
			"    `vmm_err<<FIELD1>>\n" +
			"endclass\n";

		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc1);
		TextTagPosUtils tt_utils = ini.second();
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory(null);
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1", markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());

		TestCompletionProcessor cp = new TestCompletionProcessor(
				"testVMMMacroContentAssist", file, fIndexCollectionVMMMgr);
		
		scanner.seek(tt_utils.getPosMap().get("FIELD1"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("FIELD1"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"vmm_error"}, proposals);
	}

	public void testScopedNonInheritanceAssist() {
		LogHandle log = LogFactory.getLogHandle("testScopedNonInheritanceAssist");
		String doc =
			"class my_class1;\n" +							// 1
			"    int           my_field1_class1;\n" +		// 2
			"    int           my_field2_class1;\n" +		// 3
			"endclass\n" +									// 4
			"\n" +											// 5
			"class my_class2;\n" +							// 6
			"    int           my_field1_class2;\n" +		// 7
			"    int           my_field2_class2;\n" +		// 8
			"\n" +											// 9
			"    function void foo();\n" +					// 10
			"        int v = my_<<MARK>>\n" +				// 11
			"    endfunction\n" +							// 12
			"endclass\n";									// 13
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), createOVMIndexMgr());
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		ISVDBIndexIterator index_it = cp.getIndexIterator();
		ISVDBItemIterator it = index_it.getItemIterator(new NullProgressMonitor());
		SVDBIndexValidator v = new SVDBIndexValidator();
		
		v.validateIndex(index_it.getItemIterator(new NullProgressMonitor()), SVDBIndexValidator.ExpectErrors);
		
		SVDBClassDecl my_class2 = null;
		
		List<SVDBDeclCacheItem> found = index_it.findGlobalScopeDecl(
				new NullProgressMonitor(), "my_class2", SVDBFindDefaultNameMatcher.getDefault());
		assertEquals(1, found.size());
		
		my_class2 = (SVDBClassDecl)found.get(0).getSVDBItem();
		assertNotNull(my_class2);
		
		/*
		while (it.hasNext()) {
			ISVDBItemBase it_t = it.nextItem();
			log.debug("    " + it_t.getType() + " " + SVDBItem.getName(it_t));
			if (SVDBItem.getName(it_t).equals("my_class2")) {
				my_class2 = (SVDBClassDecl)it_t;
			}
		}
		 */
		
		
		log.debug("[my_class2] " + SVDBUtil.getChildrenSize(my_class2) + " items");
		for (ISVDBItemBase it_t : my_class2.getChildren()) {
			log.debug("    [my_class2] " + it_t.getType() + " " + SVDBItem.getName(it_t));
		}
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		// TODO: at some point, my_class1 and my_class2 will not be proposals,
		// since they are types not variables 
		validateResults(new String[] {"my_class1", "my_class2",
				"my_field1_class2", "my_field2_class2"
				}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testScopedFieldContentAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class my_class1;\n" +
			"    int           my_field1_class1;\n" +
			"    int           my_field2_class1;\n" +
			"endclass\n" +
			"\n" +
			"class my_class2;\n" +
			"    int           my_field1_class2;\n" +
			"    int           my_field2_class2;\n" +
			"\n" +
			"    function void foo();\n" +
			"        my_class1 v1;\n" +
			"        v1.<<MARK>>\n" +
			"    endfunction\n" +
			"endclass\n";
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), createStandaloneIndexMgr());
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"my_field1_class1", "my_field2_class1"}, proposals);
	}

	public void testScopedFieldDerefContentAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class my_class1;\n" +
			"    int           my_field1_class1;\n" +
			"    int           my_field2_class1;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1_1;\n" +
			"    my_class1     m_cls;\n" +
			"endclass\n" +
			"\n" +
			"class my_class2;\n" +
			"    int           my_field1_class2;\n" +
			"    int           my_field2_class2;\n" +
			"    my_class1_1   v1;\n" +
			"\n" +
			"    function void foo();\n" +
			"        v1.m_cls.my_field<<MARK>>\n" +
			"    endfunction\n" +
			"endclass\n";
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), createOVMIndexMgr());
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"my_field1_class1", "my_field2_class1"}, proposals);
	}

	public void testExternScopedFieldContentAssist() {
		String doc =
			"class my_class1;\n" +
			"    int           my_field1_class1;\n" +
			"    int           my_field2_class1;\n" +
			"endclass\n" +
			"\n" +
			"class my_class2;\n" +
			"    int           my_field1_class2;\n" +
			"    int           my_field2_class2;\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"function void my_class2::foo();\n" +
			"    my_field<<MARK>>\n" +
			"endfunction\n"
			;
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), createOVMIndexMgr());
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"my_field1_class2", "my_field2_class2"}, proposals);
	}

	public void testScopedTypedefFieldContentAssist() {
		String doc =
			"class my_class1;\n" +
			"    int           my_field1_class1;\n" +
			"    int           my_field2_class1;\n" +
			"endclass\n" +
			"\n" +
			"typedef my_class1 class_t;\n" +
			"class my_class2;\n" +
			"    int           my_field1_class2;\n" +
			"    int           my_field2_class2;\n" +
			"\n" +
			"    function void foo();\n" +
			"        class_t v1;\n" +
			"        v1.<<MARK>>\n" +
			"    endfunction\n" +
			"endclass\n";
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		SVCorePlugin.getDefault().enableDebug(false);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), createOVMIndexMgr());
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"my_field1_class1", "my_field2_class1"}, proposals);
	}

	public void testScopedInheritanceAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class my_class1;\n" +
			"    int           my_field1_class1;\n" +
			"    int           my_field2_class1;\n" +
			"endclass\n" +
			"\n" +
			"class my_class2 extends my_class1;\n" +
			"    int           my_field1_class2;\n" +
			"    int           my_field2_class2;\n" +
			"\n" +
			"    function void foo();\n" +
			"        int my_<<MARK>>\n" +
			"    endfunction\n" +
			"endclass\n";
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), createOVMIndexMgr());
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		// TODO: at some point, my_class1 and my_class2 will not be proposals,
		// since they are types not variables 
		validateResults(new String[] {"my_field1_class2", "my_field2_class2",
				"my_field1_class1", "my_field2_class1",
				"my_class1", "my_class2"}, proposals);
	}

	/**
	 * Test that constructor completion works properly
	 */
	public void testConstructorCompletion() {
		LogHandle log = LogFactory.getLogHandle("testConstructorCompletion");
		String doc =
			"class my_class1;\n" +
			"    int           my_field1_class1;\n" +
			"    int           my_field2_class1;\n" +
			"    function new(int p1, int p2);\n" +
			"    endfunction\n" +
			"endclass\n" +
			"\n" +
			"class my_class2 extends my_class1;\n" +
			"    int           my_field1_class2;\n" +
			"    int           my_field2_class2;\n" +
			"    int           new_field;\n" +
			"\n" +
			"    function new(int p1);\n" +
			"    endfunction\n" +
			"\n" +
			"    function void foo();\n" +
			"        my_class1 cl1;\n" +
			"        cl1 = new<<MARK>>\n" +
			"    endfunction\n" +
			"endclass\n";
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), createOVMIndexMgr());
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("Proposal: \"" + p.getReplacement() + "\"");
		}
		
		assertEquals("Expecting one proposal", 2, proposals.size());

		SVDBTask 	new_f;
		SVDBVarDeclItem		new_field;

		if (proposals.get(0).getItem().getType() == SVDBItemType.Function) {
			new_f = (SVDBTask)proposals.get(0).getItem();
			new_field = (SVDBVarDeclItem)proposals.get(1).getItem();
		} else {
			new_f = (SVDBTask)proposals.get(1).getItem();
			new_field = (SVDBVarDeclItem)proposals.get(0).getItem();
		}
		
		log.debug("new_f parent is " + new_f.getParent().getType() + " " + 
				SVDBItem.getName(new_f.getParent()));

		assertEquals("Expect new_f name to be 'new'", "new", new_f.getName());
		assertEquals("Expect field name to be 'new_field'", "new_field", 
				SVDBItem.getName(new_field));
		
		assertEquals("Expect to get 'new' from class1", 
				"my_class1", SVDBItem.getName(new_f.getParent()));
		assertEquals("Expect to get 'new_field' from class2", 
				"my_class2", SVDBItem.getName(new_field.getParent().getParent()));
		LogFactory.removeLogHandle(log);
	}

	public void testUntriggeredClassAssist() {
		String doc = 
			"class my_class1;\n" +
			"endclass\n" +
			"\n" +
			"class my_class;\n" +
			"    <<FIELD1>>\n" +
			"endclass\n";
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		StringBIDITextScanner scanner = new StringBIDITextScanner(
				ini.second().getStrippedData());
		
		// We only look at the local index here (no OVM)
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndex);
		
		scanner.seek(ini.second().getPosMap().get("FIELD1"));

		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("FIELD1"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		// Remove any keyword proposals
		for (int i=0; i<proposals.size(); i++) {
			if (SVKeywords.isSVKeyword(proposals.get(i).getReplacement())) {
				proposals.remove(i);
				i--;
			}
		}
		
		validateResults(new String[] {"my_class", "my_class1"}, proposals);
	}

	public void testEmptyFileAssist() {
		String doc = 
			"<<FIELD1>>";
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		StringBIDITextScanner scanner = new StringBIDITextScanner(
				ini.second().getStrippedData());
		
		// We only look at the local index here (no OVM)
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndex);
		
		scanner.seek(ini.second().getPosMap().get("FIELD1"));

		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("FIELD1"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		// Remove any keyword proposals
		for (int i=0; i<proposals.size(); i++) {
			if (SVKeywords.isSVKeyword(proposals.get(i).getReplacement())) {
				proposals.remove(i);
				i--;
			}
		}
		
		validateResults(new String[] {}, proposals);
	}

	public void testUntriggeredPrefixClassAssist() {
		String doc = 
			"class my_class1;\n" +
			"endclass\n" +
			"\n" +
			"class my_class;\n" +
			"    ovm_com<<FIELD1>>\n" +
			"endclass\n";
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		StringBIDITextScanner scanner = new StringBIDITextScanner(
				ini.second().getStrippedData());

		// We only look at the local index here (no OVM)
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), createOVMIndexMgr());
		
		scanner.seek(ini.second().getPosMap().get("FIELD1"));

		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("FIELD1"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"ovm_comparer", 
				"ovm_component", "ovm_component_registry"}, proposals);
	}
	
	public void testMacroCompletion() {
		String doc =
			"class my_class extends ovm_object;\n" +
			"    `ovm_object_u<<MARK>>\n" +
			"endclass\n";
		
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		StringBIDITextScanner scanner = new StringBIDITextScanner(
				ini.second().getStrippedData());

		// We only look at the local index here (no OVM)
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), createOVMIndexMgr());
		
		scanner.seek(ini.second().getPosMap().get("MARK"));

		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"ovm_object_utils_begin", "ovm_object_utils", 
				"ovm_object_utils_end"}, proposals);
	}

	public void testFunctionNonVoidReturn() {
		String doc =
			"class my_class extends ovm_component;\n" +
			"\n" +
			"    function void build();\n" +
			"        if (get_config_ob<<MARK>>\n" +
			"\n" +
			"endclass\n";
		
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testFunctionNonVoidReturn");
		
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		StringBIDITextScanner scanner = new StringBIDITextScanner(
				ini.second().getStrippedData());

		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), createOVMIndexMgr());
		
		scanner.seek(ini.second().getPosMap().get("MARK"));

		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("Proposal: " + p.getReplacement());
		}
		
		validateResults(new String[] {"get_config_object"}, proposals);
		LogFactory.removeLogHandle(log);
	}

	public void testEndFunctionLabel() {
		String testname = "testEndFunctionLabel";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class my_class extends ovm_component;\n" +
			"\n" +
			"	function void build();\n" +
			"	endfunction : <<MARK>>\n" +
			"\n" +
			"endclass\n";
		
		
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		StringBIDITextScanner scanner = new StringBIDITextScanner(
				ini.second().getStrippedData());

		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), createOVMIndexMgr());
		
		scanner.seek(ini.second().getPosMap().get("MARK"));

		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			log.debug("Proposal: " + p.getReplacement());
		}
		
		validateResults(new String[] {"build"}, proposals);
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
