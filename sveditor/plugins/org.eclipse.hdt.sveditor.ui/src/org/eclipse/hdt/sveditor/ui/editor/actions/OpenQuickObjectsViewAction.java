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
 *     Armond Paiva - repurposed from hierarchy view to objects view
 ****************************************************************************/


package net.sf.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.ui.texteditor.TextEditorAction;

public class OpenQuickObjectsViewAction extends TextEditorAction {
	
	private SVEditor fEditor;
	
	public OpenQuickObjectsViewAction(
			ResourceBundle			bundle,
			SVEditor editor) {
		
		super(bundle, "OpenQuickObjects.", editor) ;
		
		fEditor = editor ;
	}

	@Override
	public void run() {
		// TODO: 
			
		fEditor.getQuickObjectsPresenter().showInformation();
	};

}
