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


package net.sf.sveditor.ui.editor.actions;

import java.util.List;
import java.util.ResourceBundle;

import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.open_decl.OpenDeclUtils;
import org.eclipse.hdt.sveditor.core.preproc.ISVStringPreProcessor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.TextEditorAction;

import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.scanutils.SVDocumentTextScanner;
import net.sf.sveditor.ui.views.MacroExpansionView;

public class OpenMacroExpansionAction extends TextEditorAction {
	private SVEditor				fEditor;
	private LogHandle				fLog;
	private boolean					fDebugEn = true;

	public OpenMacroExpansionAction(
			ResourceBundle			bundle,
			SVEditor				editor) {
		super(bundle, "OpenMacroExpansion.", editor);
		fLog = LogFactory.getLogHandle("OpenMacroExpansionAction");
		fEditor = editor;
		update();
	}
	
	
	@Override
	public void update() {
		if (fEditor != null) {
			ITextSelection sel = getTextSel();
			IDocument doc = getDocument();
//			try {
//			System.out.println("Selection: " + sel.getOffset() + 
//					doc.get(sel.getOffset(), 1));
//			} catch (BadLocationException e) { }
			setEnabled(true);
		} else {
			setEnabled(false); // no editor
		}
	}



	protected ITextSelection getTextSel() {
		ITextSelection sel = null;
		
		if (getTextEditor() != null) {
			ISelection sel_o = 
				getTextEditor().getSelectionProvider().getSelection();
			if (sel_o != null && sel_o instanceof ITextSelection) {
				sel = (ITextSelection)sel_o;
			} 
		}
		
		return sel;
	}

	@Override
	public void run() {
		debug("OpenMacroExpansionAction.run()");
	
		IWorkbenchWindow w = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		IWorkbenchPage p = w.getActivePage();
		MacroExpansionView m_view = null;
		
		try {
			IViewPart view = p.showView(SVUiPlugin.PLUGIN_ID + ".macroExpansionView");
			
			if (view != null) {
				m_view = (MacroExpansionView)view;
			}
		} catch (PartInitException e) {
			e.printStackTrace();
		}
		
		if (m_view == null) {
			return;
		}
		
		m_view.setContext(fEditor);
		
//		fEditor.getSite().getWorkbenchWindow().

//		Tuple<ISVDBItemBase, SVDBFile> target = findTarget();
//
//		try {
//			if (target.first() != null) {
//				fLog.debug("Open file for item \"" + SVDBItem.getName(target.first())); 
//				SVEditorUtil.openEditor(target.first());
//			} else if (target.second() != null) {
//				SVEditorUtil.openEditor(target.second().getFilePath());
//			}
//		} catch (PartInitException e) {
//			fLog.error("Failed to open declaration in editor", e);
//		}
	}
	
	protected SVDBFile getTargetFile() {
		return fEditor.getSVDBFile();
	}
	
	protected ISVDBIndexIterator getIndexIt() {
		return fEditor.getIndexIterator();
	}
	
	protected IDocument getDocument() {
		return fEditor.getDocumentProvider().getDocument(fEditor.getEditorInput());
	}
	
	protected Tuple<ISVDBItemBase, SVDBFile> findTarget() {
		IDocument doc = getDocument();
		ITextSelection sel = getTextSel();
		int offset = sel.getOffset() + sel.getLength();

		SVDocumentTextScanner 	scanner = new SVDocumentTextScanner(doc, offset);
		scanner.setSkipComments(true);
		
		ISVStringPreProcessor preproc = fEditor.createPreProcessor(
				getTextSel().getStartLine());
		
		List<Tuple<ISVDBItemBase, SVDBFile>> items = OpenDeclUtils.openDecl_2(
				getTargetFile(), 
				getTextSel().getStartLine(),
				scanner,
				preproc,
				getIndexIt());

		if (items.size() > 0) {
			return items.get(0);
		} else {
			return new Tuple<ISVDBItemBase, SVDBFile>(null, null);
		}
	}
	
	private void debug(String msg) {
		if (fDebugEn) {
			fLog.debug(msg);
		}
	}
}
