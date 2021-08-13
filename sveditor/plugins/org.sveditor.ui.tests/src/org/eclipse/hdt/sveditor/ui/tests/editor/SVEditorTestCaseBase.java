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
package org.eclipse.hdt.sveditor.ui.tests.editor;

import org.eclipse.hdt.sveditor.ui.SVEditorUtil;
import org.eclipse.hdt.sveditor.ui.editor.SVAutoIndentStrategy;
import org.eclipse.hdt.sveditor.ui.editor.SVDocumentPartitions;
import org.eclipse.hdt.sveditor.ui.editor.SVEditor;
import org.eclipse.hdt.sveditor.ui.editor.outline.SVOutlinePage;
import org.eclipse.hdt.sveditor.ui.tests.utils.editor.AutoEditTester;
import org.eclipse.hdt.sveditor.ui.tests.utils.editor.EditorTestCaseBase;

import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.jface.text.IDocument;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

public class SVEditorTestCaseBase extends EditorTestCaseBase {

	protected SVEditor findEditor(String path) {
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
	
	protected SVEditor openEditor(String path) throws PartInitException {
		IEditorPart ed = SVEditorUtil.openEditor(path);
		assertNotNull(ed);
		assertTrue((ed instanceof SVEditor));
		
		while (Display.getDefault().readAndDispatch()) {}
	
		SVEditor sv_ed = (SVEditor)ed;
		if (!fEditors.contains(sv_ed)) {
			fEditors.add(sv_ed);
		}
		
		return sv_ed;
	}

	protected Tuple<SVEditor, AutoEditTester> openAutoEditTester(String path) throws PartInitException {
		IEditorPart ed = SVEditorUtil.openEditor(path);
		assertNotNull(ed);
		assertTrue((ed instanceof SVEditor));
		
		while (Display.getDefault().readAndDispatch()) {}
	
		SVEditor sv_ed = (SVEditor)ed;
		if (!fEditors.contains(sv_ed)) {
			fEditors.add(sv_ed);
		}
		
		AutoEditTester auto_edit = new AutoEditTester(
				sv_ed.getDocument(), 
				SVDocumentPartitions.SV_PARTITIONING);
		
		auto_edit.setAutoEditStrategy(
				IDocument.DEFAULT_CONTENT_TYPE, 
				new SVAutoIndentStrategy(null, SVDocumentPartitions.SV_PARTITIONING));
		
		return new Tuple<SVEditor, AutoEditTester>(sv_ed, auto_edit);
	}
	
	protected SVOutlinePage getOutlineView(IEditorPart editor) throws PartInitException {
		IViewPart outline_v = editor.getSite().getPage().showView("org.eclipse.ui.views.ContentOutline");
		assertNotNull(outline_v);
		
		while (Display.getDefault().readAndDispatch()) {}
		
		Object ret = editor.getAdapter(IContentOutlinePage.class);
		
		assertTrue(ret instanceof SVOutlinePage);
		
		return (SVOutlinePage)ret;
	}
}
