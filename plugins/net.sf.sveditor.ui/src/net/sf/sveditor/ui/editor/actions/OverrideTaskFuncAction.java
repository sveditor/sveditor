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


package net.sf.sveditor.ui.editor.actions;

import java.util.ResourceBundle;

import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.ui.texteditor.TextEditorAction;

public class OverrideTaskFuncAction extends TextEditorAction { 
	private OverrideTaskFuncImpl			fImpl;
	
	public OverrideTaskFuncAction(
			ResourceBundle			bundle,
			String					prefix,
			SVEditor				editor) {
		super(bundle, prefix, editor);
		fImpl = new OverrideTaskFuncImpl(editor);
		update();
	}
	
	@Override
	public void update() {
		super.update();
	}
	
	@Override
	public void run() {
		super.run();
		fImpl.run();
	}
}
