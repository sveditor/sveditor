/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.editor.SVEditor;

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
