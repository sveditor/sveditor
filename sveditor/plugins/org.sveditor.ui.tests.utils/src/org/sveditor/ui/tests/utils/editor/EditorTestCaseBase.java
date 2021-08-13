/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.ui.tests.utils.editor;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import org.sveditor.core.tests.TestIndexCacheFactory;
import org.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.Tuple;
import org.sveditor.core.db.index.SVDBIndexRegistry;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.ITextEditor;

public class EditorTestCaseBase extends TestCase {
	protected LogHandle				fLog;
	protected List<IProject>		fProjects;
	protected List<ITextEditor>		fEditors;
	protected File					fTmpDir;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		
		fLog = LogFactory.getLogHandle(getName());
		
		cleanupWorkspace();
		
		fProjects = new ArrayList<IProject>();
		fEditors = new ArrayList<ITextEditor>();
		
		fTmpDir = TestUtils.createTempDir();
		File db = new File(fTmpDir, "db");
		
		assertTrue(db.mkdirs());
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(new TestIndexCacheFactory(db));
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		for (ITextEditor t : fEditors) {
			t.close(false);
		}

		// Wait for the editors to close
		while (Display.getDefault().readAndDispatch()) {}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.close();
	
		SVCorePlugin.getJobMgr().dispose();
		
		for (IProject p : fProjects) {
			TestUtils.deleteProject(getName(), p);
		}
		
		if (fTmpDir != null && fTmpDir.exists()) {
			TestUtils.delete(fTmpDir);
		}
		
		cleanupWorkspace();
	}
	
	protected void addProject(IProject p) {
		fProjects.add(p);
	}
	
	protected void addEditor(ITextEditor editor) {
		if (!fEditors.contains(editor)) {
			fEditors.add(editor);
		}
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
