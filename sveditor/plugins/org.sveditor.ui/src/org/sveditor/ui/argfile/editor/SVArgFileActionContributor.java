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
package org.sveditor.ui.argfile.editor;

import java.util.ResourceBundle;

import org.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.editors.text.TextEditorActionContributor;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.RetargetTextEditorAction;

public class SVArgFileActionContributor extends TextEditorActionContributor {
	protected RetargetTextEditorAction fOpenDeclarationAction;
	protected RetargetTextEditorAction fToggleCommentAction;

	
	public SVArgFileActionContributor() {
		super();
		ResourceBundle bundle = SVUiPlugin.getDefault().getResources();
		
		fOpenDeclarationAction = new RetargetTextEditorAction(
				bundle, "ArgFileOpenFile.");
		fOpenDeclarationAction.setActionDefinitionId(
				"org.sveditor.ui.argfile.editor.open.file");
		
		fToggleCommentAction = new RetargetTextEditorAction(
				bundle, "ArgFileToggleComment.");
		fToggleCommentAction.setActionDefinitionId(
				SVUiPlugin.PLUGIN_ID + ".ArgFileToggleComment");
	}
	
	public void contributeToMenu(IMenuManager mm) {
		super.contributeToMenu(mm);
	
		IMenuManager editMenu = 
				mm.findMenuUsingPath(IWorkbenchActionConstants.M_EDIT);
		if (editMenu != null) {
			editMenu.add(new Separator());
			editMenu.add(fOpenDeclarationAction);
		}
		/*
		 */
	}
	
	public void init(IActionBars bars) {
		super.init(bars);
	
		IMenuManager menuManager = bars.getMenuManager();
		IMenuManager editMenu = menuManager.findMenuUsingPath(
				IWorkbenchActionConstants.M_EDIT);
		
		if (editMenu != null) {
			editMenu.add(new Separator());
			editMenu.add(fOpenDeclarationAction);
			editMenu.add(fToggleCommentAction);
		}
		/*
		 */
	}

	private void doSetActiveEditor(IEditorPart part) {
		super.setActiveEditor(part);

		ITextEditor editor= null;
		if (part instanceof ITextEditor) {
			editor= (ITextEditor) part;
//			fOpenDeclarationAction.setAction(getAction(editor, "ArgFileOpenFile"));
			fOpenDeclarationAction.setAction(getAction(editor, 
					SVUiPlugin.PLUGIN_ID + ".svArgFileOpenFile"));
			fToggleCommentAction.setAction(getAction(editor,
					SVUiPlugin.PLUGIN_ID + ".svArgFileToggleComment"));
		}
		/*
		 */
	}

	public void setActiveEditor(IEditorPart part) {
		super.setActiveEditor(part);
		doSetActiveEditor(part);
	}

	/*
	 * @see IEditorActionBarContributor#dispose()
	 */
	public void dispose() {
		doSetActiveEditor(null);
		super.dispose();
	}
}
