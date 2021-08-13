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


package org.eclipse.hdt.sveditor.ui.tests.editor;

import java.io.File;

import org.eclipse.hdt.sveditor.core.tests.CoreReleaseTests;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.SVDBTestUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;
import org.eclipse.hdt.sveditor.ui.SVEditorUtil;
import org.eclipse.hdt.sveditor.ui.SVUiPlugin;
import org.eclipse.hdt.sveditor.ui.editor.SVEditor;
import org.eclipse.hdt.sveditor.ui.editor.actions.OpenDeclarationAction;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexCollection;
import org.eclipse.hdt.sveditor.core.db.project.SVDBPath;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;

public class TestUserLevelOperations extends SVCoreTestCaseBase {
	
	public void testOpenClassDeclaration() throws CoreException, InterruptedException {
		SVCorePlugin.getDefault().enableDebug(false);
		cleanupWorkspace();

		CoreReleaseTests.clearErrors();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		// Create a new project for the 
		File test_dir = new File(fTmpDir, "testArgFileIndex");
		if (test_dir.exists()) {
			assertTrue(test_dir.delete());
		}
		assertTrue(test_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/ovm.zip", test_dir);
		File xbus = new File(test_dir, "ovm/examples/xbus");
		
		IProject project_dir = TestUtils.createProject("xbus", xbus);
		
		// Setup appropriate project settings
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData p_data = p_mgr.getProjectData(project_dir);
		
		// Add an argument-file path for the XBus example
		SVProjectFileWrapper p_wrapper = p_data.getProjectFileWrapper().duplicate();
		p_wrapper.getArgFilePaths().add(new SVDBPath("${workspace_loc}/xbus/examples/compile_questa_sv.f"));
		p_data.setProjectFileWrapper(p_wrapper);
		
		// Now, open xbus/examples/xbus_demo_tb.sv
		SVDBIndexCollection project_index = p_data.getProjectIndexMgr();
		
		// force index loading
		project_index.loadIndex(new NullProgressMonitor());

		IEditorPart xbus_demo_tb = SVEditorUtil.openEditor("${workspace_loc}/xbus/examples/xbus_demo_tb.sv");
		assertNotNull(xbus_demo_tb);
		assertTrue((xbus_demo_tb instanceof SVEditor));
		SVEditor sveditor = (SVEditor)xbus_demo_tb;
		

		// Propagate events
		while (Display.getDefault().readAndDispatch()) {}
		
		OpenDeclarationAction od_action = (OpenDeclarationAction)
			sveditor.getAction(SVUiPlugin.PLUGIN_ID + ".svOpenEditorAction");
		
		IDocument doc = sveditor.getDocument();
		int idx = doc.get().indexOf("ovm_env");
		sveditor.getSelectionProvider().setSelection(new TextSelection(idx, "ovm_env".length()));
		//sveditor.setSelection(idx, idx+"ovm_env".length(), true);

		ISVDBIndexIterator index_it = sveditor.getIndexIterator();
	
//		System.out.println("--> Dump index");
//		ISVDBItemIterator item_it = index_it.getItemIterator(new NullProgressMonitor());
//		while (item_it.hasNext()) {
//			/*ISVDBItemBase it_t = */ item_it.nextItem();
			// System.out.println("    it_t=" + it_t.getName());
//		}
//		System.out.println("<-- Dump index");

		while (Display.getDefault().readAndDispatch()) {}
		
		// sveditor.getSelectionProvider().getSelection()
		
		od_action.run();

		while (Display.getDefault().readAndDispatch()) {}

		// Now, need to validate
		SVEditor ovm_env = findEditor("ovm_env.svh");
		assertNotNull(ovm_env);
		
		// Now, confirm no errors
		SVDBFile ovm_env_f = ovm_env.getSVDBFile();
		SVDBTestUtils.assertNoErrWarn(ovm_env_f);
		SVDBTestUtils.assertFileHasElements(ovm_env_f, "ovm_env");
		
		
		
		
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
	
	private SVEditor findEditor(String path) {
		SVEditor ret = null;
		
		IWorkbenchWindow w = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		for (IWorkbenchPage p : w.getPages()) {
			for (IEditorReference ed : p.getEditorReferences()) {
				if (ed.getName().endsWith(path)) {
					IEditorPart ed_p = ed.getEditor(true);
					if (ed_p instanceof SVEditor) {
						ret = (SVEditor)ed_p;
						break;
					}
				}
			}
		}
		return ret;
	}
}
