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


package org.sveditor.ui.tests.editor;

import org.sveditor.core.tests.CoreReleaseTests;
import org.sveditor.core.tests.utils.TestUtils;
import org.sveditor.ui.SVEditorUtil;
import org.sveditor.ui.editor.SVEditor;
import org.sveditor.ui.editor.outline.SVOutlineContent;
import org.sveditor.ui.editor.outline.SVOutlinePage;
import org.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.SVDBClassDecl;
import org.sveditor.core.db.SVDBClockingBlock;
import org.sveditor.core.db.SVDBConstraint;
import org.sveditor.core.db.SVDBCovergroup;
import org.sveditor.core.db.SVDBCoverpoint;
import org.sveditor.core.db.SVDBCoverpointCross;
import org.sveditor.core.db.SVDBFunction;
import org.sveditor.core.db.SVDBGenerateBlock;
import org.sveditor.core.db.SVDBGenerateIf;
import org.sveditor.core.db.SVDBInterfaceDecl;
import org.sveditor.core.db.SVDBItem;
import org.sveditor.core.db.SVDBModIfcInstItem;
import org.sveditor.core.db.SVDBModportDecl;
import org.sveditor.core.db.SVDBModportItem;
import org.sveditor.core.db.SVDBModuleDecl;
import org.sveditor.core.db.SVDBPackageDecl;
import org.sveditor.core.db.SVDBProgramDecl;
import org.sveditor.core.db.SVDBProperty;
import org.sveditor.core.db.SVDBSequence;
import org.sveditor.core.db.SVDBTask;
import org.sveditor.core.db.stmt.SVDBAlwaysStmt;
import org.sveditor.core.db.stmt.SVDBAssertStmt;
import org.sveditor.core.db.stmt.SVDBFinalStmt;
import org.sveditor.core.db.stmt.SVDBInitialStmt;
import org.sveditor.core.db.stmt.SVDBTypedefStmt;
import org.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

public class TestOutlineViewOperations extends SVEditorTestCaseBase {
	
	public void testOutlineViewSelectionPreservation_1() throws CoreException, InterruptedException, BadLocationException {
		String testname = "testOutlineViewSelectionPreservation_1";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		cleanupWorkspace();

		CoreReleaseTests.clearErrors();
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		IProject project = TestUtils.createProject(testname);
		addProject(project);
		
		// Create simple class file
		String class_file =
				"class cls1;\n" +
				"	extern function void f1();\n" +
				"endclass\n" +
				"\n" +
				"\n" +
				"\n" +
				"function void cls1::f1;\n" +
				"endfunction\n" +
				"\n"
				;
		
		TestUtils.copy(class_file, project.getFile("cls1.svh"));
		
		// Setup appropriate project settings
//		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
//		SVDBProjectData p_data = p_mgr.getProjectData(project);
		
		IEditorPart cls1_svh = SVEditorUtil.openEditor("${workspace_loc}/" + testname + "/cls1.svh");
		assertNotNull(cls1_svh);
		assertTrue((cls1_svh instanceof SVEditor));
		SVEditor editor = (SVEditor)cls1_svh;
		addEditor(editor);
		
		// Propagate events
		while (Display.getDefault().readAndDispatch()) {}
		
		IViewPart outline_v = cls1_svh.getSite().getPage().showView("org.eclipse.ui.views.ContentOutline");
		assertNotNull(outline_v);
		while (Display.getDefault().readAndDispatch()) {}
		
		SVOutlinePage outline = (SVOutlinePage)editor.getAdapter(IContentOutlinePage.class);

		ITreeContentProvider cp = outline.getContentProvider();
		SVOutlineContent content = new SVOutlineContent(editor.getSVDBFile(), null);
		cp.inputChanged(null, null, content);
		
		Object root_roots[] = cp.getElements(content);
		Object roots[] = cp.getChildren(root_roots[0]);
		
		for (Object r : roots) {
			log.debug("r=" + r);
		}
	
		// Select the Function element
		log.debug("--> Set selection to Function Definition");
		outline.clearIgnoreSelectionChange();
		assertTrue(root_roots[1] instanceof SVDBFunction);
		assertEquals("cls1::f1", ((SVDBFunction)root_roots[1]).getName());
		
		outline.setSelection(new StructuredSelection(root_roots[1]));
		while (Display.getDefault().readAndDispatch()) {}
		log.debug("<-- Set selection to Function Definition");
		
		ISelection sel = outline.getSelection();
		
		assertTrue((sel instanceof IStructuredSelection));
		assertTrue(((IStructuredSelection)sel).getFirstElement() instanceof SVDBFunction);
		SVDBFunction f = (SVDBFunction)((IStructuredSelection)sel).getFirstElement();
		assertEquals("cls1::f1", f.getName());

		ITextSelection text_sel = (ITextSelection)editor.getSelectionProvider().getSelection();
		log.debug("editor sel: " + text_sel.getStartLine());
	
		IDocument doc = editor.getDocument();
		IRegion region = doc.getLineInformationOfOffset(text_sel.getOffset());
		String line = doc.get(region.getOffset(), region.getLength());
		assertTrue(line.contains("function void cls1::f1"));
		assertFalse(line.contains("extern"));
	
		// Now, modify the document
		log.debug("--> Add 'class cls2' to document");
		editor.setSelection(0, 0, true);
		while (Display.getDefault().readAndDispatch()) {}
		text_sel = (ITextSelection)editor.getSelectionProvider().getSelection();
		log.debug("Selection: " + text_sel.getStartLine());
		doc.replace(0, 0, "class cls2; endclass\n");
		while (Display.getDefault().readAndDispatch()) {}
		text_sel = (ITextSelection)editor.getSelectionProvider().getSelection();

		Thread.sleep(100);
		while (Display.getDefault().readAndDispatch()) {}
		log.debug("<-- Add 'class cls2' to document");
		
		text_sel = (ITextSelection)editor.getSelectionProvider().getSelection();
		assertEquals(0, text_sel.getStartLine());
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}
	
	public void testOutlineViewModule() throws CoreException, InterruptedException, BadLocationException {
		String testname = "testOutlineViewModule";
		LogHandle log = LogFactory.getLogHandle(testname);
		log.setDebugLevel(LogHandle.LEVEL_MAX);
		SVCorePlugin.getDefault().enableDebug(false);
		cleanupWorkspace();
		
		CoreReleaseTests.clearErrors();
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project = TestUtils.createProject(testname);
		addProject(project);
		
		// Module containing a number of common items
		String class_file =
				"module m1 ();\n" +
						"	function void f1(); endfunction \n" +
						"	task mytask (); endtask\n" +
						"	initial begin : named_initial end\n" +
						"	initial begin  end\n" +
						"	final begin : named_final end\n" +
						"	final begin  end\n" +
						"	always_comb begin : named_always_comb end\n" +
						"	always_comb begin end\n" +
						"	always @(posedge clk) begin : named_always_clk end\n" +
						"	always @(posedge clk) begin  end\n" +
						"	always_ff @(posedge clk) begin : named_always_ff end\n" +
						"	always_ff @(posedge clk) begin  end\n" +
						"	always_latch begin : named_always_latch end\n" +
						"	always_latch begin end\n" +
						"	submodule sm1 ();\n" +
						"endmodule\n" +
						"\n"
						;
		// Expected data
		String [] expected_names = {
				"f1(): void",
				"mytask()",
				"named_initial: initial",
				"initial",
				"named_final: final",
				"final",
				"named_always_comb: always",
				"always",
				"named_always_clk: @(posedge clk)",
				"@(posedge clk)",
				"named_always_ff: @(posedge clk)",
				"@(posedge clk)",
				"named_always_latch: always",
				"always",
				"sm1: submodule"
		};
		
		TestUtils.copy(class_file, project.getFile("testfile.sv"));
		
		// Setup appropriate project settings
		IEditorPart testfile_sv = SVEditorUtil.openEditor("${workspace_loc}/" + testname + "/testfile.sv");
		assertNotNull(testfile_sv);
		assertTrue((testfile_sv instanceof SVEditor));
		SVEditor editor = (SVEditor)testfile_sv;
		addEditor(editor);
		
		// Propagate events
		while (Display.getDefault().readAndDispatch()) {}
		
		IViewPart outline_v = testfile_sv.getSite().getPage().showView("org.eclipse.ui.views.ContentOutline");
		assertNotNull(outline_v);
		while (Display.getDefault().readAndDispatch()) {}
		
		SVOutlinePage outline = (SVOutlinePage)editor.getAdapter(IContentOutlinePage.class);
		
		ITreeContentProvider cp = outline.getContentProvider();
		SVOutlineContent content = new SVOutlineContent(editor.getSVDBFile(), null);
		cp.inputChanged(null, null, content);
		
		Object root_roots[] = cp.getElements(content);
		
		// Checking Module 1 - m1
		Object m1_children[] = cp.getChildren(root_roots[0]);
		assertEquals(root_roots.length, 1);
		assertTrue(root_roots[0] instanceof SVDBModuleDecl);
		assertEquals(((SVDBItem) root_roots[0]).getName(), "m1");
		assertEquals(m1_children.length, 15);
		
		// Check the text
		SVTreeLabelProvider lp = new SVTreeLabelProvider();
		for (int i=0; i<expected_names.length; i++)  {
			assertEquals(expected_names[i], lp.getStyledText(m1_children[i]).getString());
		}
		
		// Check the type and text in the outline
		assertTrue(m1_children[ 0] instanceof SVDBFunction);
		assertTrue(m1_children[ 1] instanceof SVDBTask);
		assertTrue(m1_children[ 2] instanceof SVDBInitialStmt);
		assertTrue(m1_children[ 3] instanceof SVDBInitialStmt);
		assertTrue(m1_children[ 4] instanceof SVDBFinalStmt);
		assertTrue(m1_children[ 5] instanceof SVDBFinalStmt);
		assertTrue(m1_children[ 6] instanceof SVDBAlwaysStmt);
		assertTrue(m1_children[ 7] instanceof SVDBAlwaysStmt);
		assertTrue(m1_children[ 8] instanceof SVDBAlwaysStmt);
		assertTrue(m1_children[ 9] instanceof SVDBAlwaysStmt);
		assertTrue(m1_children[10] instanceof SVDBAlwaysStmt);
		assertTrue(m1_children[11] instanceof SVDBAlwaysStmt);
		assertTrue(m1_children[12] instanceof SVDBAlwaysStmt);
		assertTrue(m1_children[13] instanceof SVDBAlwaysStmt);
		assertTrue(m1_children[14] instanceof SVDBModIfcInstItem);

		assertEquals(0, CoreReleaseTests.getErrors().size());
	}
	
	public void testOutlineViewModuleGenerate() throws CoreException, InterruptedException, BadLocationException {
		String testname = "testOutlineViewModuleGenerate";
		LogHandle log = LogFactory.getLogHandle(testname);
		log.setDebugLevel(LogHandle.LEVEL_MAX);
		SVCorePlugin.getDefault().enableDebug(false);
		cleanupWorkspace();
		
		CoreReleaseTests.clearErrors();
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project = TestUtils.createProject(testname);
		addProject(project);
		
		// Module containing a number of common items
		String class_file =
				"module module_name();\n" +
						"		for (i=0; i<10; i++)\n" +
						"		begin \n" +
						"			module_name mn0 ();\n" +
						"		end\n" +
						"		for (i=0; i<10; i++)\n" +
						"		begin : namedfor\n" +
						"			module_name mn1 ();\n" +
						"		end\n" +
						"		generate \n" +
						"			for ( i = 0 ;  i < 5 ;  i ++ ) \n" +
						"			begin : gen_for\n" +
						"				always_ff @(posedge clk)  begin : named_always\n" +
						"						a  <=  n;\n" +
						"				end\n" +
						"			end\n" +
						"		endgenerate\n" +
						"		generate \n" +
						"		begin : namedgen\n" +
						"			for (i=0; i<10; i++)\n" +
						"			begin :for1\n" +
						"				module_name mn2 ();\n" +
						"			end\n" +
						"			if (1)\n" +
						"				module_name mn3 ();\n" +
						"			else\n" +
						"				module_name mn4 ();\n" +
						"			if (1) begin : namedif\n" +
						"				module_name mn5 ();\n" +
						"			end\n" +
						"			else if (1) begin : namedelse\n" +
						"				module_name mn6 ();\n" +
						"			end\n" +
						"		end\n" +
						"		endgenerate\n" +
						"		if (1)\n" +
						"			module_name mn7 ();\n" +
						"		else\n" +
						"			module_name mn8 ();\n" +
						"		if (1) begin : namedif2\n" +
						"			module_name mn9 ();\n" +
						"		end\n" +
						"		else if (1) begin : namedelse\n" +
						"			module_name mn10 ();\n" +
						"		end\n" +
						"	endmodule\n" +
						"\n"
						;
		// Expected data
		String [] names_root = {
				"for",
				"namedfor: for",
				"generate",
				"namedgen: generate",
				"if",
				"namedif2: if"
		};
		
		TestUtils.copy(class_file, project.getFile("testfile.sv"));
		
		// Setup appropriate project settings
		IEditorPart testfile_sv = SVEditorUtil.openEditor("${workspace_loc}/" + testname + "/testfile.sv");
		assertNotNull(testfile_sv);
		assertTrue((testfile_sv instanceof SVEditor));
		SVEditor editor = (SVEditor)testfile_sv;
		addEditor(editor);
		
		// Propagate events
		while (Display.getDefault().readAndDispatch()) {}
		
		IViewPart outline_v = testfile_sv.getSite().getPage().showView("org.eclipse.ui.views.ContentOutline");
		assertNotNull(outline_v);
		while (Display.getDefault().readAndDispatch()) {}
		
		SVOutlinePage outline = (SVOutlinePage)editor.getAdapter(IContentOutlinePage.class);
		
		ITreeContentProvider cp = outline.getContentProvider();
		SVOutlineContent content = new SVOutlineContent(editor.getSVDBFile(), null);
		cp.inputChanged(null, null, content);
		
		Object root_roots[] = cp.getElements(content);
		
		// Checking Module 1 - m1
		assertEquals(root_roots.length, 1);
		assertTrue(root_roots[0] instanceof SVDBModuleDecl);
		assertEquals(((SVDBItem) root_roots[0]).getName(), "module_name");

		// Start with the children
		Object children0[] = cp.getChildren(root_roots[0]);
		assertEquals(names_root.length, children0.length);
		
		// Check the text in the outline
		SVTreeLabelProvider lp = new SVTreeLabelProvider();
		for (int i=0; i<names_root.length; i++)  {
			assertEquals(names_root[i], lp.getStyledText(children0[i]).getString());
		}
		
		// Check the type in the outline
		assertTrue(children0[ 0] instanceof SVDBGenerateBlock);
		assertTrue(children0[ 1] instanceof SVDBGenerateBlock);
		assertTrue(children0[ 2] instanceof SVDBGenerateBlock);
		assertTrue(children0[ 3] instanceof SVDBGenerateBlock);
		assertTrue(children0[ 4] instanceof SVDBGenerateIf);
		assertTrue(children0[ 5] instanceof SVDBGenerateIf);

		// Now for the children of the children
		Object children1[] = cp.getChildren(children0[0]);
		assertEquals(1, children1.length);
		assertEquals("mn0: module_name", lp.getStyledText(children1[0]).getString());
		assertTrue(children1[0] instanceof SVDBModIfcInstItem);
		
		children1 = cp.getChildren(children0[1]);
		assertEquals(children1.length, 1);
		assertEquals("mn1: module_name", lp.getStyledText(children1[0]).getString());
		assertTrue(children1[0] instanceof SVDBModIfcInstItem);

		children1 = cp.getChildren(children0[2]);
		assertEquals(1, children1.length);
		assertEquals("gen_for: for", lp.getStyledText(children1[0]).getString());
		assertTrue(children1[0] instanceof SVDBGenerateBlock);

		Object []children2 = cp.getChildren(children1[0]);
		assertEquals(1, children2.length);
		assertEquals("named_always: @(posedge clk)", lp.getStyledText(children2[0]).getString());
		assertTrue(children2[0] instanceof SVDBAlwaysStmt);

		children1 = cp.getChildren(children0[3]);
		assertEquals(3, children1.length);
		assertEquals("for1: for", lp.getStyledText(children1[0]).getString());
		assertTrue(children1[0] instanceof SVDBGenerateBlock);

		children2 = cp.getChildren(children1[0]);
		assertEquals(1, children2.length);
		assertEquals("mn2: module_name", lp.getStyledText(children2[0]).getString());
		assertTrue(children2[0] instanceof SVDBModIfcInstItem);

		assertEquals("if", lp.getStyledText(children1[1]).getString());
		assertTrue(children1[1] instanceof SVDBGenerateIf);
		assertEquals("namedif: if", lp.getStyledText(children1[2]).getString());
		assertTrue(children1[2] instanceof SVDBGenerateIf);


		assertEquals(0, CoreReleaseTests.getErrors().size());
	}
	
	public void testOutlineBasicClass() throws CoreException, InterruptedException, BadLocationException {
		String testname = "testOutlineBasicClass";
		LogHandle log = LogFactory.getLogHandle(testname);
		log.setDebugLevel(LogHandle.LEVEL_MAX);
		SVCorePlugin.getDefault().enableDebug(false);
		cleanupWorkspace();
		
		CoreReleaseTests.clearErrors();
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project = TestUtils.createProject(testname);
		addProject(project);
		
		// Module containing a number of common items
		String class_file =
				"class classa extends classc;\n" +
						"		\n" +
						"		function int init (input logic a);\n" +
						"		endfunction\n" +
						"		\n" +
						"		task task_name (input logic port_list);\n" +
						"			\n" +
						"		endtask\n" +
						"		\n" +
						"		constraint c_cons  {};\n" +
						"		enum { red, green, blue } color;\n" +
						"		typedef enum { red, green, blue } e_color;\n" +
						"		covergroup cg1 @(posedge clk);\n" +
						"			coverpoint color;\n" +
						"			c1: coverpoint color;\n" +
						"			cross color;\n" +
						"			c2: cross color;\n" +
						"		endgroup		\n" +
						"		cp1: cover property (write(address));\n" +
						"	endclass\n" +
						"\n"
						;
		// Expected data
		String [] expected_names = {
				"init(logic): int",
				"task_name(logic)",
				"c_cons",
				"color: <<ANONYMOUS>>",
				"e_color",
				"cg1",
				"cp1",
		};
		
		TestUtils.copy(class_file, project.getFile("testfile.sv"));
		
		// Setup appropriate project settings
		IEditorPart testfile_sv = SVEditorUtil.openEditor("${workspace_loc}/" + testname + "/testfile.sv");
		assertNotNull(testfile_sv);
		assertTrue((testfile_sv instanceof SVEditor));
		SVEditor editor = (SVEditor)testfile_sv;
		addEditor(editor);
		
		// Propagate events
		while (Display.getDefault().readAndDispatch()) {}
		
		IViewPart outline_v = testfile_sv.getSite().getPage().showView("org.eclipse.ui.views.ContentOutline");
		assertNotNull(outline_v);
		while (Display.getDefault().readAndDispatch()) {}
		
		SVOutlinePage outline = (SVOutlinePage)editor.getAdapter(IContentOutlinePage.class);
		
		ITreeContentProvider cp = outline.getContentProvider();
		SVOutlineContent content = new SVOutlineContent(editor.getSVDBFile(), null);
		cp.inputChanged(null, null, content);
		
		Object root_roots[] = cp.getElements(content);
		
		// Checking top
		Object children0[] = cp.getChildren(root_roots[0]);
		assertEquals(1, root_roots.length);
		assertTrue(root_roots[0] instanceof SVDBClassDecl);
		assertEquals(((SVDBItem) root_roots[0]).getName(), "classa");
		assertEquals(expected_names.length, children0.length);
		
		// Check the text
		SVTreeLabelProvider lp = new SVTreeLabelProvider();
		for (int i=0; i<expected_names.length; i++)  {
			assertEquals(expected_names[i], lp.getStyledText(children0[i]).getString());
		}
		
		// Check the type and text in the outline
		assertTrue(children0[ 0] instanceof SVDBFunction);
		assertTrue(children0[ 1] instanceof SVDBTask);
		assertTrue(children0[ 2] instanceof SVDBConstraint);
		assertTrue(children0[ 3] instanceof SVDBVarDeclItem);
		assertTrue(children0[ 4] instanceof SVDBTypedefStmt);
		assertTrue(children0[ 5] instanceof SVDBCovergroup);

		Object [] children1 = cp.getChildren(children0[5]);
		assertEquals(4, children1.length);
		assertEquals("coverpoint", lp.getStyledText(children1[0]).getString());
		assertTrue(children1[0] instanceof SVDBCoverpoint);
		
		assertEquals("c1", lp.getStyledText(children1[1]).getString());
		assertTrue(children1[1] instanceof SVDBCoverpoint);

		assertEquals("cross", lp.getStyledText(children1[2]).getString());
		assertTrue(children1[2] instanceof SVDBCoverpointCross);
		
		assertEquals("c2", lp.getStyledText(children1[3]).getString());
		assertTrue(children1[3] instanceof SVDBCoverpointCross);

		assertEquals(0, CoreReleaseTests.getErrors().size());
	}
	
	public void testOutlinePkg() throws CoreException, InterruptedException, BadLocationException {
		String testname = "testOutlinePkg";
		LogHandle log = LogFactory.getLogHandle(testname);
		log.setDebugLevel(LogHandle.LEVEL_MAX);
		SVCorePlugin.getDefault().enableDebug(false);
		cleanupWorkspace();
		
		CoreReleaseTests.clearErrors();
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project = TestUtils.createProject(testname);
		addProject(project);
		
		// Module containing a number of common items
		String class_file =
				"package p;\n" +
						"	typedef enum { FALSE, TRUE } bool_t;\n" +
						"			struct {\n" +
						"		bit b;\n" +
						"	} plainstruct;\n" +
						"	typedef struct {\n" +
						"		bit b;\n" +
						"	} typestruct;\n" +
						"endpackage\n" +
						"\n"
						;
		// Expected data
		String [] expected_names = {
				"bool_t",
				"plainstruct: <<ANONYMOUS>>",
				"typestruct"
		};
		
		TestUtils.copy(class_file, project.getFile("testfile.sv"));
		
		// Setup appropriate project settings
		IEditorPart testfile_sv = SVEditorUtil.openEditor("${workspace_loc}/" + testname + "/testfile.sv");
		assertNotNull(testfile_sv);
		assertTrue((testfile_sv instanceof SVEditor));
		SVEditor editor = (SVEditor)testfile_sv;
		addEditor(editor);
		
		// Propagate events
		while (Display.getDefault().readAndDispatch()) {}
		
		IViewPart outline_v = testfile_sv.getSite().getPage().showView("org.eclipse.ui.views.ContentOutline");
		assertNotNull(outline_v);
		while (Display.getDefault().readAndDispatch()) {}
		
		SVOutlinePage outline = (SVOutlinePage)editor.getAdapter(IContentOutlinePage.class);
		
		ITreeContentProvider cp = outline.getContentProvider();
		SVOutlineContent content = new SVOutlineContent(editor.getSVDBFile(), null);
		cp.inputChanged(null, null, content);
		
		Object root_roots[] = cp.getElements(content);
		
		// Checking top
		Object children0[] = cp.getChildren(root_roots[0]);
		assertEquals(1, root_roots.length);
		assertTrue(root_roots[0] instanceof SVDBPackageDecl);
		assertEquals(((SVDBItem) root_roots[0]).getName(), "p");
		assertEquals(expected_names.length, children0.length);
		
		// Check the text
		SVTreeLabelProvider lp = new SVTreeLabelProvider();
		for (int i=0; i<expected_names.length; i++)  {
			assertEquals(expected_names[i], lp.getStyledText(children0[i]).getString());
		}
		
		// Check the type and text in the outline
		assertTrue(children0[ 0] instanceof SVDBTypedefStmt);
		assertTrue(children0[ 1] instanceof SVDBVarDeclItem);
		assertTrue(children0[ 2] instanceof SVDBTypedefStmt);
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}
	
	public void testOutlineViewSeqProp() throws CoreException, InterruptedException, BadLocationException {
		String testname = "testOutlineViewSeqProp";
		LogHandle log = LogFactory.getLogHandle(testname);
		log.setDebugLevel(LogHandle.LEVEL_MAX);
		SVCorePlugin.getDefault().enableDebug(false);
		cleanupWorkspace();
		
		CoreReleaseTests.clearErrors();
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project = TestUtils.createProject(testname);
		addProject(project);
		
		// Module containing a number of common items
		String class_file =
				"program pgm;\n" +
						"		sequence seq1;\n" +
						"			@(posedge clk) a ##1 b ##1 c;\n" +
						"		endsequence\n" +
						"			\n" +
						"		assert property ( @(posedge clk) a |=> b );\n" +
						"\n" +
						"		ap_prop1: assert property ( @(posedge clk) a |=> b );\n" +
						"		\n" +
						"		ap_prop2: assert property( prop () );\n" +
						"\n" +
						"		property prop;\n" +
						"			a |=> b;\n" +
						"		endproperty\n" +
						"	endprogram\n" +
						"\n"
						;
		// Expected data
		String [] expected_names = {
				"seq1",
				"assert",
				"assert: ap_prop1",
				"assert: ap_prop2",
				"prop"
		};
		
		TestUtils.copy(class_file, project.getFile("testfile.sv"));
		
		// Setup appropriate project settings
		IEditorPart testfile_sv = SVEditorUtil.openEditor("${workspace_loc}/" + testname + "/testfile.sv");
		assertNotNull(testfile_sv);
		assertTrue((testfile_sv instanceof SVEditor));
		SVEditor editor = (SVEditor)testfile_sv;
		addEditor(editor);
		
		// Propagate events
		while (Display.getDefault().readAndDispatch()) {}
		
		IViewPart outline_v = testfile_sv.getSite().getPage().showView("org.eclipse.ui.views.ContentOutline");
		assertNotNull(outline_v);
		while (Display.getDefault().readAndDispatch()) {}
		
		SVOutlinePage outline = (SVOutlinePage)editor.getAdapter(IContentOutlinePage.class);
		
		ITreeContentProvider cp = outline.getContentProvider();
		SVOutlineContent content = new SVOutlineContent(editor.getSVDBFile(), null);
		cp.inputChanged(null, null, content);
		
		Object root_roots[] = cp.getElements(content);
		
		// Checking top
		Object children0[] = cp.getChildren(root_roots[0]);
		assertEquals(1, root_roots.length);
		assertTrue(root_roots[0] instanceof SVDBProgramDecl);
		assertEquals(((SVDBItem) root_roots[0]).getName(), "pgm");
		assertEquals(expected_names.length, children0.length);
		
		// Check the text
		SVTreeLabelProvider lp = new SVTreeLabelProvider();
		for (int i=0; i<expected_names.length; i++)  {
			assertEquals(expected_names[i], lp.getStyledText(children0[i]).getString());
		}
		
		// Check the type and text in the outline
		assertTrue(children0[ 0] instanceof SVDBSequence);
		assertTrue(children0[ 1] instanceof SVDBAssertStmt);
		assertTrue(children0[ 2] instanceof SVDBAssertStmt);
		assertTrue(children0[ 3] instanceof SVDBAssertStmt);
		assertTrue(children0[ 4] instanceof SVDBProperty);
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}
	
	
	/**
	 * Check for items we intentionally hide
	 * @throws CoreException
	 * @throws InterruptedException
	 * @throws BadLocationException
	 */
	public void testOutlineViewHidden() throws CoreException, InterruptedException, BadLocationException {
		String testname = "testOutlineViewHidden";
		LogHandle log = LogFactory.getLogHandle(testname);
		log.setDebugLevel(LogHandle.LEVEL_MAX);
		SVCorePlugin.getDefault().enableDebug(false);
		cleanupWorkspace();
		
		CoreReleaseTests.clearErrors();
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project = TestUtils.createProject(testname);
		addProject(project);
		
		// Module containing a number of common items
		String class_file =
				"module amodule;\n" +
						"	timeunit 1ns ;\n" +
						"	timeprecision 1ps ;\n" +
						"endmodule\n" +
						"\n"
						;
		// Expected data
		String [] expected_names = {
		};
		
		TestUtils.copy(class_file, project.getFile("testfile.sv"));
		
		// Setup appropriate project settings
		IEditorPart testfile_sv = SVEditorUtil.openEditor("${workspace_loc}/" + testname + "/testfile.sv");
		assertNotNull(testfile_sv);
		assertTrue((testfile_sv instanceof SVEditor));
		SVEditor editor = (SVEditor)testfile_sv;
		addEditor(editor);
		
		// Propagate events
		while (Display.getDefault().readAndDispatch()) {}
		
		IViewPart outline_v = testfile_sv.getSite().getPage().showView("org.eclipse.ui.views.ContentOutline");
		assertNotNull(outline_v);
		while (Display.getDefault().readAndDispatch()) {}
		
		SVOutlinePage outline = (SVOutlinePage)editor.getAdapter(IContentOutlinePage.class);
		
		ITreeContentProvider cp = outline.getContentProvider();
		SVOutlineContent content = new SVOutlineContent(editor.getSVDBFile(), null);
		cp.inputChanged(null, null, content);
		
		Object root_roots[] = cp.getElements(content);
		
		// Checking top
		Object children0[] = cp.getChildren(root_roots[0]);
		assertEquals(1, root_roots.length);
		assertTrue(root_roots[0] instanceof SVDBModuleDecl);
		assertEquals(((SVDBItem) root_roots[0]).getName(), "amodule");
		assertEquals(expected_names.length+2, children0.length);
		
		// Check the text
		SVTreeLabelProvider lp = new SVTreeLabelProvider();
		for (int i=0; i<expected_names.length; i++)  {
			assertEquals(expected_names[i], lp.getStyledText(children0[i]).getString());
		}
		
		// Check the type and text in the outline
//		assertTrue(children0[ 0] instanceof SVDBProperty);
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}
	
	
	public void testOutlineViewInterface() throws CoreException, InterruptedException, BadLocationException {
		String testname = "testOutlineViewInterface";
		LogHandle log = LogFactory.getLogHandle(testname);
		log.setDebugLevel(LogHandle.LEVEL_MAX);
		SVCorePlugin.getDefault().enableDebug(false);
		cleanupWorkspace();
		
		CoreReleaseTests.clearErrors();
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project = TestUtils.createProject(testname);
		addProject(project);
		
		// Module containing a number of common items
		String class_file =
				"interface A_Bus( input bit clk );\n" +
						"		wire req, gnt;\n" +
						"		wire [7:0] addr, data;\n" +
						"		clocking sb @(posedge clk);\n" +
						"			input gnt;\n" +
						"			output req, addr;\n" +
						"			inout data;\n" +
						"			property p1; req ##[1:3] gnt; endproperty\n" +
						"		endclocking\n" +
						"		modport STB ( clocking sb ); // synchronous testbench modport\n" +
						"	endinterface\n" +
						"\n"
						;
		// Expected data
		String [] expected_names = {
				"req: wire",
				"gnt: wire",
				"addr: wire",
				"data: wire",
				"sb",
				"modport"
		};
		
		TestUtils.copy(class_file, project.getFile("testfile.sv"));
		
		// Setup appropriate project settings
		IEditorPart testfile_sv = SVEditorUtil.openEditor("${workspace_loc}/" + testname + "/testfile.sv");
		assertNotNull(testfile_sv);
		assertTrue((testfile_sv instanceof SVEditor));
		SVEditor editor = (SVEditor)testfile_sv;
		addEditor(editor);
		
		// Propagate events
		while (Display.getDefault().readAndDispatch()) {}
		
		IViewPart outline_v = testfile_sv.getSite().getPage().showView("org.eclipse.ui.views.ContentOutline");
		assertNotNull(outline_v);
		while (Display.getDefault().readAndDispatch()) {}
		
		SVOutlinePage outline = (SVOutlinePage)editor.getAdapter(IContentOutlinePage.class);
		
		ITreeContentProvider cp = outline.getContentProvider();
		SVOutlineContent content = new SVOutlineContent(editor.getSVDBFile(), null);
		cp.inputChanged(null, null, content);
		
		Object root_roots[] = cp.getElements(content);
		
		// Checking top
		Object children0[] = cp.getChildren(root_roots[0]);
		assertEquals(1, root_roots.length);
		assertTrue(root_roots[0] instanceof SVDBInterfaceDecl);
		assertEquals("A_Bus", ((SVDBItem) root_roots[0]).getName());
		assertEquals(expected_names.length, children0.length);
		
		// Check the text
		SVTreeLabelProvider lp = new SVTreeLabelProvider();
		for (int i=0; i<expected_names.length; i++)  {
			assertEquals(expected_names[i], lp.getStyledText(children0[i]).getString());
		}
		
		// Check the type and text in the outline
		assertTrue(children0[ 0] instanceof SVDBVarDeclItem);
		assertTrue(children0[ 1] instanceof SVDBVarDeclItem);
		assertTrue(children0[ 2] instanceof SVDBVarDeclItem);
		assertTrue(children0[ 3] instanceof SVDBVarDeclItem);
		assertTrue(children0[ 4] instanceof SVDBClockingBlock);
		assertTrue(children0[ 5] instanceof SVDBModportDecl);
		
		Object [] children1 = cp.getChildren(children0[4]);
		assertEquals(1, children1.length);
		assertEquals("p1", lp.getStyledText(children1[0]).getString());
		assertTrue(children1[0] instanceof SVDBProperty);
		
		children1 = cp.getChildren(children0[5]);
		assertEquals(1, children1.length);
		assertEquals("STB", lp.getStyledText(children1[0]).getString());
		assertTrue(children1[0] instanceof SVDBModportItem);
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
	}
	
	private void cleanupWorkspace() throws CoreException {
		IWorkbenchWindow w = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		for (IWorkbenchPage p : w.getPages()) {
			p.closeAllEditors(true);
		}
		
		// TODO: close all open projects
		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		for (IProject p : root.getProjects()) {
			p.delete(true, new NullProgressMonitor());
		}
	}
	
}
