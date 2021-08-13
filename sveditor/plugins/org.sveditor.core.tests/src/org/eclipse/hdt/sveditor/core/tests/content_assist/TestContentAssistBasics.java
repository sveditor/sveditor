/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.tests.content_assist;

import java.io.File;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;

import junit.framework.TestCase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

public class TestContentAssistBasics extends SVCoreTestCaseBase {
	
	private ISVDBIndex createOVMIndex() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File ovm_dir = new File(fTmpDir, "ovm_dir");
		TestCase.assertTrue(ovm_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/ovm.zip", ovm_dir);
		
		TestUtils.copy(
				"+incdir+" + ovm_dir.getAbsolutePath() + "/ovm/src\n" +
				ovm_dir.getAbsolutePath() + "/ovm/src/ovm_pkg.sv\n",
				new File(ovm_dir, "ovm.f"));
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(), 
				getName(),
				new File(ovm_dir, "ovm.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE,
				null);
		
		return index;
	}
	
	private ISVDBIndex createVMMIndex() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File ovm_dir = new File(fTmpDir, "vvm_dir");
		TestCase.assertTrue(ovm_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/vvm.zip", ovm_dir);
	
		// TODO:
		TestUtils.copy(
				"+incdir+" + ovm_dir.getAbsolutePath() + "/ovm/src\n" +
				ovm_dir.getAbsolutePath() + "/ovm/src/ovm_pkg.sv\n",
				new File(ovm_dir, "ovm.f"));
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(), 
				getName(),
				new File(ovm_dir, "ovm.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE,
				null);
		
		return index;
	}	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testOVMMacroContentAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
//		SVCorePlugin.getDefault().setDebugLevel(ILogLevel.LEVEL_OFF);
		
		String doc = 
			"class my_class;\n" +
			"    `ovm_componen<<MARK>>\n" +
			"endclass\n";
	
		ContentAssistTests.runTest(this, 
				createOVMIndex(),
				doc, 
				"ovm_component_utils", "ovm_component_param_utils", 
				"ovm_component_utils_begin", "ovm_component_param_utils_begin", 
				"ovm_component_utils_end", "ovm_component_new_func", 
				"ovm_component_factory_create_func", "ovm_component_registry",
				"ovm_component_registry_internal", "ovm_component_registry_param",
				"OVM_COMPONENT_SVH");
	}

	/**
	 * Fails: Is the failure due to the PluginLib or to VMM?
	 */
	public void disabled_testVMMMacroContentAssist() {
		String doc = 
			"class my_class;\n" +
			"    `vmm_err<<MARK>>\n" +
			"endclass\n";
		SVCorePlugin.getDefault().enableDebug(false);
		
		ContentAssistTests.runTest(this, 
				createVMMIndex(), 
				doc,
				"vmm_error");
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
		SVCorePlugin.getDefault().enableDebug(false);
		
		ContentAssistTests.runTest(this, doc, "my_class1", "my_class2",
				"my_field1_class2", "my_field2_class2");
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
		
		ContentAssistTests.runTest(this, doc, 
				"my_field1_class1", "my_field2_class1");
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
		ContentAssistTests.runTest(this, doc, 
				"my_field1_class1", "my_field2_class1");
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
		ContentAssistTests.runTest(this, doc, 
				"my_field1_class2", "my_field2_class2");
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
		ContentAssistTests.runTest(this, doc, 
				"my_field1_class1", "my_field2_class1");
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
		ContentAssistTests.runTest(this, doc, 
				"my_field1_class2", "my_field2_class2",
				"my_field1_class1", "my_field2_class1",
				"my_class1", "my_class2");
	}

	/**
	 * Test that constructor completion works properly
	 */
	public void DISABLED_testConstructorCompletion() {
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
		ContentAssistTests.runTest(this, doc, "");

//		Tuple<SVDBFile, TextTagPosUtils> ini = contentAssistSetup(doc);
//		
//		StringBIDITextScanner scanner = new StringBIDITextScanner(ini.second().getStrippedData());
//		TestCompletionProcessor cp = new TestCompletionProcessor(ini.first(), createOVMIndexMgr());
//		
//		scanner.seek(ini.second().getPosMap().get("MARK"));
//		
//		
//		cp.computeProposals(scanner, ini.first(), 
//				ini.second().getLineMap().get("MARK"));
//		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
//		
//		for (SVCompletionProposal p : proposals) {
//			log.debug("Proposal: \"" + p.getReplacement() + "\"");
//		}
//		
//		assertEquals("Expecting one proposal", 2, proposals.size());
//
//		SVDBTask 	new_f;
//		SVDBVarDeclItem		new_field;
//
//		if (proposals.get(0).getItem().getType() == SVDBItemType.Function) {
//			new_f = (SVDBTask)proposals.get(0).getItem();
//			new_field = (SVDBVarDeclItem)proposals.get(1).getItem();
//		} else {
//			new_f = (SVDBTask)proposals.get(1).getItem();
//			new_field = (SVDBVarDeclItem)proposals.get(0).getItem();
//		}
//		
//		log.debug("new_f parent is " + new_f.getParent().getType() + " " + 
//				SVDBItem.getName(new_f.getParent()));
//
//		assertEquals("Expect new_f name to be 'new'", "new", new_f.getName());
//		assertEquals("Expect field name to be 'new_field'", "new_field", 
//				SVDBItem.getName(new_field));
//		
//		assertEquals("Expect to get 'new' from class1", 
//				"my_class1", SVDBItem.getName(new_f.getParent()));
//		assertEquals("Expect to get 'new_field' from class2", 
//				"my_class2", SVDBItem.getName(new_field.getParent().getParent()));
//		LogFactory.removeLogHandle(log);
	}

	public void testUntriggeredClassAssist() {
		String doc = 
			"class my_class1;\n" +
			"endclass\n" +
			"\n" +
			"class my_class;\n" +
			"    <<MARK>>\n" +
			"endclass\n";
		
		ContentAssistTests.runTest(this, doc, true, 
				new String[] {"my_class", "my_class1",
						"process", "semaphore"});
	}

	public void testEmptyFileAssist() {
		String doc = 
			"<<MARK>>";
		ContentAssistTests.runTest(this, doc, true, new String[] {
				"process", "semaphore"
		});
	}

	public void testUntriggeredPrefixClassAssist() {
		String doc = 
			"class my_class1;\n" +
			"endclass\n" +
			"\n" +
			"class my_class;\n" +
			"    ovm_com<<MARK>>\n" +
			"endclass\n";
		SVCorePlugin.getDefault().enableDebug(false);
		
		ContentAssistTests.runTest(this, 
				createOVMIndex(),
				doc,
				"ovm_comparer", "ovm_component", "ovm_component_registry");
	}
	
	public void testMacroCompletion() {
		String doc =
			"class my_class extends ovm_object;\n" +
			"    `ovm_object_u<<MARK>>\n" +
			"endclass\n";
		
		ContentAssistTests.runTest(this, 
				createOVMIndex(),
				doc, 
				"ovm_object_utils_begin", "ovm_object_utils", 
				"ovm_object_utils_end");
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
		ContentAssistTests.runTest(this, 
				createOVMIndex(),
				doc, 
				"get_config_object");
	}

	public void testEndFunctionLabel() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class my_class extends ovm_component;\n" +
			"\n" +
			"	function void build();\n" +
			"	endfunction : <<MARK>>\n" +
			"\n" +
			"endclass\n";
		
		ContentAssistTests.runTest(this, 
				createOVMIndex(),
				doc, 
				"build");
	}

}
