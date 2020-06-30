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


package net.sf.sveditor.core.tests.content_assist;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;

import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestContentAssistBehavioralBlock extends SVCoreTestCaseBase {
	
	
	/**
	 * Test that basic macro content assist works
	 */
	public void testAssignRHS() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class foobar;\n" +
			"	int		AAAA;\n" +
			"	int		AABB;\n" +
			"	int		BBCC;\n" +
			"endclass\n" +
			"\n" +
			"\n" +
			"class my_class;\n" +
			"	foobar		m_field;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"class my_class2;\n" +
			"	foobar		m_field2;\n" +
			"\n" +
			"	extern task my_task();\n" +
			"\n" +
			"endclass\n" +
			"\n" +
			"task my_class::my_task(output int param);\n" +
			"	param = m_<<MARK>>\n" +
			"endtask\n"
			;

		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"m_field");
		/*
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory();
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBFile file = factory.parse(tt_utils.openStream(), "doc1", markers);
		StringBIDITextScanner scanner = new StringBIDITextScanner(tt_utils.getStrippedData());
		
		for (ISVDBItemBase it : file.getChildren()) {
			log.debug("    it: " + it.getType() + " " + SVDBItem.getName(it));
		}

		TestCompletionProcessor cp = new TestCompletionProcessor(
				log, file, new FileIndexIterator(file));
		
		scanner.seek(tt_utils.getPosMap().get("MARK"));

		cp.computeProposals(scanner, file, tt_utils.getLineMap().get("MARK"));
		List<SVCompletionProposal> proposals = cp.getCompletionProposals();
		
		ContentAssistTests.validateResults(new String[] {"m_field"}, proposals);
		LogFactory.removeLogHandle(log);
		 */
	}

	public void testBlockLocalVariable() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"\n" +
			"class my_class;\n" +
			"	foobar		m_field;\n" +
			"\n" +
			"	task my_task();\n" +
			"		int a;\n" +
			"		begin\n" +
			"			int AAAA;\n" +
			"			int AABB;\n" +
			"			int BBCC;\n" +
			"\n" +
			"			AA<<MARK>>\n" +
			"		end\n" +
			"	endtask\n" +
			"\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
		
		/*
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory();
		
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
		
		ContentAssistTests.validateResults(new String[] {"AAAA", "AABB"}, proposals);
		LogFactory.removeLogHandle(log);
		 */
	}

	public void testFieldRefBlockLocalVariable() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"\n" +
			"class my_type;\n" +
			"	int AAAA;\n" +
			"	int AABB;\n" +
			"	int BBCC;\n" +
			"endclass\n" +
			"\n" +
			"class my_class;\n" +
			"	foobar		m_field;\n" +
			"\n" +
			"	task my_task();\n" +
			"		int a;\n" +
			"		begin\n" +
			"			my_type f;\n" +
			"\n" +
			"			f.AA<<MARK>>\n" +
			"		end\n" +
			"	endtask\n" +
			"\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"AAAA", "AABB");
			
		/*
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory();
		
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
		
		ContentAssistTests.validateResults(new String[] {"AAAA", "AABB"}, proposals);
		LogFactory.removeLogHandle(log);
		 */
	}

	public void testLessEqualAssist() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"\n" +
			"class my_class;\n" +
			"	foobar		m_field1;\n" +
			"	foobar		m_field2;\n" +
			"\n" +
			"	task my_task();\n" +
			"		int a;\n" +
			"		if (a <= m_<<MARK>>\n" +
			"	endtask\n" +
			"\n" +
			"endclass\n"
			;
			
		ContentAssistTests.runTest(getName(), fCacheFactory, doc, 
				"m_field1", "m_field2");
		/*
		TextTagPosUtils tt_utils = new TextTagPosUtils(new StringInputStream(doc1));
		ISVDBFileFactory factory = SVCorePlugin.createFileFactory();
		
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
		
		ContentAssistTests.validateResults(new String[] {"m_field1", "m_field2"}, proposals);
		LogFactory.removeLogHandle(log);
		 */
	}

	public void testStructFieldAssistInForIfScope() {
		String testname = "testStructFieldAssistInForIfScope";
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class cls1;\n" +
			" typedef struct {\n" +
			" int AA;\n" +
			" int AB;\n" +
			" int BA;\n" +
			" int BB;\n" +
			" } my_struct;\n" +
			"\n" +
			" my_struct			f1;\n" +
			"\n" +
			" function void func();\n" +
			" 	for (int i=0; i<5; i++) begin\n" +
			" 		if (i == 2) begin\n" +
			"			myfunc(f1.<<MARK>>\n" +
			" 		end\n" +
			"	end\n" +
			" endfunction\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"AA", "AB", "BA", "BB");
	}
	
	public void testStructFieldAssistInForScope() {
		String testname = "testStructFieldAssistInForScope";
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"class cls1;\n" +
			" typedef struct {\n" +
			" int AA;\n" +
			" int AB;\n" +
			" int BA;\n" +
			" int BB;\n" +
			" } my_struct;\n" +
			"\n" +
			" my_struct			f1;\n" +
			"\n" +
			" function void func();\n" +
			" 	for (int i=0; i<5; i++) begin\n" +
			"		myfunc(f1.<<MARK>>\n" +
			"	end\n" +
			" endfunction\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"AA", "AB", "BA", "BB");
	}
	
	public void testPackageScopeGlobalVarDecl() {
		String testname = "testGlobalVarDecl";
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			"package foo;\n" +
			"	int AA;\n" +
			"	int AB;\n" +
			"	int BA;\n" +
			"	int BB;\n" +
			"endpackage\n" +
			"\n" +
			"class cls1;\n" +
			"\n" +
			" my_struct			f1;\n" +
			"\n" +
			" function void func();\n" +
			"	A<<MARK>>\n" +
			" endfunction\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"AA", "AB");
	}
	
	public void testRootScopeGlobalVarDecl() {
		String testname = "testRootScopeGlobalVarDecl";
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			// These fields might effectively be in a
			// package scope, but due to code structure
			// would appear as shown below
			"int AA;\n" +
			"int AB;\n" +
			"int BA;\n" +
			"int BB;\n" +
			"\n" +
			"class cls1;\n" +
			"\n" +
			" my_struct			f1;\n" +
			"\n" +
			" function void func();\n" +
			"	A<<MARK>>\n" +
			" endfunction\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"AA", "AB");
	}

	public void testRootScopeGlobalClassVarDecl() {
		String testname = "testRootScopeGlobalClassVarDecl";
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			// These fields might effectively be in a
			// package scope, but due to code structure
			// would appear as shown below
			"\n" +
			"class c1;\n" +
			"	int AA;\n" +
			"	int AB;\n" +
			"	int BA;\n" +
			"	int BB;\n" +
			"endclass\n" +
			"\n" +
			"const c1 c1_inst = foo();\n" +
			"\n" +
			"class cls1;\n" +
			"\n" +
			" my_struct			f1;\n" +
			"\n" +
			" function void func();\n" +
			"	c1_inst.A<<MARK>>\n" +
			" endfunction\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"AA", "AB");
	}
	
	public void testRootScopeGlobalClassVarDecl_2() {
		String testname = "testRootScopeGlobalClassVarDecl_2";
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			// These fields might effectively be in a
			// package scope, but due to code structure
			// would appear as shown below
			"\n" +
			"class c1;\n" +
			"	int AA;\n" +
			"	int AB;\n" +
			"	int BA;\n" +
			"	int BB;\n" +
			"endclass\n" +
			"\n" +
			"const c1 c1_inst = foo();\n" +
			"\n" +
			"class cls1;\n" +
			"\n" +
			" my_struct			f1;\n" +
			"\n" +
			" function void func();\n" +
			"	c1_<<MARK>>\n" +
			" endfunction\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"c1_inst");
	}	

	public void testOtherSideArrPartSelectEq() {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		
		String doc =
			// These fields might effectively be in a
			// package scope, but due to code structure
			// would appear as shown below
			"\n" +
			"class c1;\n" +
			"	int A_arr[];\n" +
			"endclass\n" +
			"\n" +
			"const c1 c1_inst = foo();\n" +
			"\n" +
			"class cls1;\n" +
			"\n" +
			"\n" +
			" function void func();\n" +
			"	int AA, AB, BA, BB;\n" +
			"	c1_inst.A_arr[2] = A<<MARK>>\n" +
			" endfunction\n" +
			"endclass\n"
			;
		
		ContentAssistTests.runTest(testname, fCacheFactory, doc, 
				"AA", "AB");
	}
}
