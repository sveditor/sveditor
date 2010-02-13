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


package net.sf.sveditor.ui.editor;

import java.util.ResourceBundle;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.editors.text.TextEditorActionContributor;
import org.eclipse.ui.part.EditorActionBarContributor;
import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;
import org.eclipse.ui.texteditor.RetargetTextEditorAction;

public class SVActionContributor extends TextEditorActionContributor {
	
	protected RetargetTextEditorAction fContentAssistProposal;
	protected RetargetTextEditorAction fContentAssistTip;
	protected RetargetTextEditorAction fContentFormatProposal;
	protected RetargetTextEditorAction fIndentAction;
	
	protected RetargetTextEditorAction fOpenDeclarationAction;
	protected RetargetTextEditorAction fOpenTypeHierarchyAction;
	
	protected MenuManager			   fSourceMenu;

	public SVActionContributor() {
		super();
		ResourceBundle bundle = SVUiPlugin.getDefault().getResources();
		
		fContentAssistProposal = new RetargetTextEditorAction(
				bundle, "ContentAssistProposal.");
		fContentAssistProposal.setActionDefinitionId(
				ITextEditorActionDefinitionIds.CONTENT_ASSIST_PROPOSALS);
		
		fOpenDeclarationAction = new RetargetTextEditorAction(
				bundle, "OpenDeclaration.");
		fOpenDeclarationAction.setActionDefinitionId(
				"net.sf.sveditor.ui.editor.open.declaration");

		fOpenTypeHierarchyAction = new RetargetTextEditorAction(
				bundle, "OpenTypeHierarchy.");
		fOpenTypeHierarchyAction.setActionDefinitionId(
				"net.sf.sveditor.ui.editor.open.type.hierarchy");

		fIndentAction = new RetargetTextEditorAction(bundle, "Indent.");
		fIndentAction.setActionDefinitionId("net.sf.sveditor.ui.indent");
		

		fContentFormatProposal = new RetargetTextEditorAction(
				bundle, "ContentFormatProposal.");
		fContentAssistTip = new RetargetTextEditorAction(bundle,
			"ContentAssistTip.");
	}

	public void contributeToMenu(IMenuManager mm) {
		IMenuManager editMenu = 
			mm.findMenuUsingPath(IWorkbenchActionConstants.M_EDIT);
		if (editMenu != null) {
			editMenu.add(new Separator());
			editMenu.add(fContentAssistProposal);
			editMenu.add(fContentFormatProposal);
			editMenu.add(fContentAssistTip);
			editMenu.add(fOpenDeclarationAction);
			editMenu.add(fOpenTypeHierarchyAction);
		}
	}
	
	/*
	 * @see IEditorActionBarContributor#init(IActionBars)
	 */
	public void init(IActionBars bars) {
		super.init(bars);

		IMenuManager menuManager = bars.getMenuManager();
		IMenuManager editMenu = menuManager.findMenuUsingPath(
				IWorkbenchActionConstants.M_EDIT);
		
		if (editMenu != null) {
			editMenu.add(new Separator());
			editMenu.add(fContentAssistProposal);
			editMenu.add(fContentAssistTip);
		}	
	}
	
	/**
	 * Sets the active editor to this contributor. This updates the actions to
	 * reflect the SQL editor.
	 * 
	 * @see EditorActionBarContributor#setActiveEditor(org.eclipse.ui.IEditorPart)
	 */
	private void doSetActiveEditor(IEditorPart part) {
		super.setActiveEditor(part);

		ITextEditor editor= null;
		if (part instanceof ITextEditor)
			editor= (ITextEditor) part;

		fContentAssistProposal.setAction(getAction(editor, "ContentAssistProposal")); //$NON-NLS-1$
		fContentAssistTip.setAction(getAction(editor, "ContentAssistTip")); //$NON-NLS-1$
		fOpenDeclarationAction.setAction(getAction(editor, "OpenDeclaration"));
		fOpenTypeHierarchyAction.setAction(getAction(editor, "OpenTypeHierarchy"));
	}

	/*
	 * @see IEditorActionBarContributor#setActiveEditor(IEditorPart)
	 */
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
