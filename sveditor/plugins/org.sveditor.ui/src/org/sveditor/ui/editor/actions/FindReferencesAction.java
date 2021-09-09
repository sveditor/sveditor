/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import org.sveditor.ui.editor.SVEditor;

import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.eclipse.ui.texteditor.TextEditorAction;

public class FindReferencesAction extends TextEditorAction {
	private SVEditor				fEditor;
	private LogHandle				fLog;
	private boolean					fDebugEn = true;

	public FindReferencesAction(
			ResourceBundle			bundle,
			SVEditor				editor) {
		super(bundle, "FindReferences.", editor);
		fLog = LogFactory.getLogHandle("FindReferencesAction");
		fEditor = editor;
		update();
	}

	@Override
	public void run() {
		System.out.println("FindReferencesAction");
		super.run();
	}

	
}
