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


package net.sf.sveditor.ui.tests.editor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFunction;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.utils.TestUtils;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.editor.SVOutlinePage;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
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
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

public class TestOutlineViewOperations extends EditorTestCaseBase {
	
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
		Object roots[] = cp.getElements(editor.getSVDBFile());
		
		for (Object r : roots) {
			log.debug("r=" + r);
		}
	
		// Select the Function element
		log.debug("--> Set selection to Function Definition");
		outline.clearIgnoreSelectionChange();
		assertTrue(roots[1] instanceof SVDBFunction);
		assertEquals("cls1::f1", ((SVDBFunction)roots[1]).getName());
		
		outline.setSelection(new StructuredSelection(roots[1]));
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
