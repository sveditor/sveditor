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
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.content_assist.SVCompletionProposal;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.SVDBVarDeclItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.Activator;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class ContentAssistBasics extends TestCase {
	private SVDBIndexCollectionMgr		fIndexCollectionOVMMgr;
	private SVDBIndexCollectionMgr		fIndexCollectionVMMMgr;
	private ContentAssistIndex			fIndex;
	private File						fTmpDir;
	
	@Override
	public void setUp() {
		fTmpDir = TestUtils.createTempDir();
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		
		utils.copyBundleDirToFS("/data/basic_content_assist_project", fTmpDir);

		String pname = "basic_content_assist_project";
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		fIndexCollectionOVMMgr = new SVDBIndexCollectionMgr(pname);
		fIndex = new ContentAssistIndex();
		fIndexCollectionOVMMgr.addLibraryPath(fIndex);
		fIndexCollectionOVMMgr.addPluginLibrary(
				rgy.findCreateIndex(pname, Activator.OVM_LIBRARY_ID, 
						SVDBPluginLibIndexFactory.TYPE, null));

		fIndexCollectionVMMMgr = new SVDBIndexCollectionMgr(pname);
		fIndexCollectionVMMMgr.addLibraryPath(fIndex);
		fIndexCollectionVMMMgr.addPluginLibrary(
				rgy.findCreateIndex(pname, Activator.VMM_LIBRARY_ID, 
						SVDBPluginLibIndexFactory.TYPE, null));

		// Force database loading
		fIndexCollectionOVMMgr.getItemIterator();
		fIndexCollectionVMMMgr.getItemIterator();
				
	}
	
	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		fTmpDir.delete();
	}
	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testOVMMacroContentAssist() {
		String doc1 = 
			"class my_class;\n" +
			"    `ovm_componen<<FIELD1>>\n" +
			"endclass\n";
		
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.getDefault().createFileFactory(null);
		
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1");
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());

		TestCompletionProcessor cp = new TestCompletionProcessor(file, fIndexCollectionOVMMgr);
		
		scanner.seek(tt_utils.getPosMap().get("FIELD1"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("FIELD1"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"ovm_component_utils", "ovm_component_param_utils", 
				"ovm_component_utils_begin", "ovm_component_param_utils_begin", 
				"ovm_component_utils_end", "ovm_component_new_func", 
				"ovm_component_factory_create_func", "ovm_component_registry",
				"ovm_component_registry_internal", "ovm_component_registry_param"}, proposals);
	}

	public void testVMMMacroContentAssist() {
		String doc1 = 
			"class my_class;\n" +
			"    `vmm_err<<FIELD1>>\n" +
			"endclass\n";

		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.getDefault().createFileFactory(null);
		
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1");
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());

		TestCompletionProcessor cp = new TestCompletionProcessor(file, fIndexCollectionVMMMgr);
		
		scanner.seek(tt_utils.getPosMap().get("FIELD1"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("FIELD1"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"vmm_error"}, proposals);
	}

	public void testScopedNonInheritanceAssist() {
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
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndexCollectionOVMMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		ISVDBIndexIterator index_it = cp.getIndexIterator();
		ISVDBItemIterator<SVDBItem> it = index_it.getItemIterator();
		
		SVDBModIfcClassDecl my_class2 = null;
		
		while (it.hasNext()) {
			SVDBItem it_t = it.nextItem();
			System.out.println("    " + it_t.getType() + " " + it_t.getName());
			if (it_t.getName().equals("my_class2")) {
				my_class2 = (SVDBModIfcClassDecl)it_t;
			}
		}
		
		System.out.println("[my_class2] " + my_class2.getItems().size() + " items");
		for (SVDBItem it_t : my_class2.getItems()) {
			System.out.println("    [my_class2] " + it_t.getType() + " " + it_t.getName());
		}
		
		
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		// TODO: at some point, my_class1 and my_class2 will not be proposals,
		// since they are types not variables 
		validateResults(new String[] {"my_class1", "my_class2",
				"my_field1_class2", "my_field2_class2"
				}, proposals);
	}

	public void testScopedFieldContentAssist() {
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
		
		SVCorePlugin.getDefault().enableDebug(true);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndexCollectionOVMMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"my_field1_class1", "my_field2_class1"}, proposals);
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
		SVCorePlugin.getDefault().enableDebug(true);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndexCollectionOVMMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"my_field1_class1", "my_field2_class1"}, proposals);
	}

	public void testScopedInheritanceAssist() {
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
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndexCollectionOVMMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		// TODO: at some point, my_class1 and my_class2 will not be proposals,
		// since they are types not variables 
		if (SVCorePlugin.getDefault().fUseParserFactory) {
			validateResults(new String[] {"my_field1_class2", "my_field2_class2",
					"my_field1_class1", "my_field2_class1",
					"my_class1", "my_class2"}, proposals);
		} else {
			// Scanner still produces "my_" as a proposal
			validateResults(new String[] {"my_field1_class2", "my_field2_class2", "my_",
					"my_field1_class1", "my_field2_class1",
					"my_class1", "my_class2"}, proposals);
		}
	}

	/**
	 * Test that constructor completion works properly
	 */
	public void testConstructorCompletion() {
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
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndexCollectionOVMMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));
		
		
		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		for (SVCompletionProposal p : proposals) {
			System.out.println("Proposal: \"" + p.getReplacement() + "\"");
		}
		
		assertEquals("Expecting two proposals", 2, proposals.size());

		SVDBTaskFuncScope 	new_f;
		SVDBVarDeclItem		new_field;

		if (proposals.get(0).getItem().getType() == SVDBItemType.Function) {
			new_f = (SVDBTaskFuncScope)proposals.get(0).getItem();
			new_field = (SVDBVarDeclItem)proposals.get(1).getItem();
		} else {
			new_f = (SVDBTaskFuncScope)proposals.get(1).getItem();
			new_field = (SVDBVarDeclItem)proposals.get(0).getItem();
		}
		
		assertEquals("Expect new_f name to be 'new'", "new", new_f.getName());
		assertEquals("Expect field name to be 'new_field'", "new_field", new_field.getName());
		
		assertEquals("Expect to get 'new' from class1", 
				"my_class1", new_f.getParent().getName());
		assertEquals("Expect to get 'new_field' from class2", 
				"my_class2", new_field.getParent().getName());
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
		
		validateResults(new String[] {"my_class", "my_class1"}, proposals);
	}

	public void testUntriggeredPrefixClassAssist() {
		String doc = 
			"class my_class1;\n" +
			"endclass\n" +
			"\n" +
			"class my_class;\n" +
			"    ovm_com<<FIELD1>>\n" +
			"endclass\n";
		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
		StringBIDITextScanner scanner = new StringBIDITextScanner(
				ini.second().getStrippedData());

		// We only look at the local index here (no OVM)
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndexCollectionOVMMgr);
		
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
		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), fIndexCollectionOVMMgr);
		
		scanner.seek(ini.second().getPosMap().get("MARK"));

		cp.computeProposals(scanner, ini.first(), 
				ini.second().getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		validateResults(new String[] {"ovm_object_utils_begin", "ovm_object_utils", 
				"ovm_object_utils_end"}, proposals);
	}

	
	/*************** Utility Methods ********************/
	private Tuple<SVDBFile, TextTagPosUtils> contentAssistSetup(String doc) {
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc));
		ISVDBFileFactory factory = SVCorePlugin.getDefault().createFileFactory(null);
		
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc");
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
