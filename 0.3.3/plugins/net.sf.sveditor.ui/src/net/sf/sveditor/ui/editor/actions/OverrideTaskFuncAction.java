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

import java.util.ArrayList;
import java.util.List;
import java.util.ResourceBundle;

import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.ui.texteditor.TextEditorAction;

public class OverrideTaskFuncAction extends TextEditorAction 
	implements IOverrideMethodsTargetProvider { 
	private OverrideTaskFuncImpl			fImpl;
	private SVEditor						fEditor;
	
	public OverrideTaskFuncAction(
			ResourceBundle			bundle,
			String					prefix,
			SVEditor				editor) {
		super(bundle, prefix, editor);
		fImpl = new OverrideTaskFuncImpl(editor, this);
		fEditor = editor;
		update();
	}
	
	@Override
	public void run() {
		super.run();
		fImpl.run();
	}

	public List<SVDBTaskFuncScope> getTargets(ISVDBScopeItem active_scope) {
		OverrideMethodsDialog dlg = null;
		
		try {
			dlg = new OverrideMethodsDialog(
					fEditor.getSite().getShell(),
					(SVDBModIfcClassDecl)active_scope, fEditor.getIndexIterator());
		} catch (Exception e) {
			e.printStackTrace();
			return null;
		}

		dlg.setBlockOnOpen(true);
		
		dlg.open();
		
		if (dlg.getResult() == null) {
			return null;
		}
		
		List<SVDBTaskFuncScope> ret = new ArrayList<SVDBTaskFuncScope>();
		for (Object o : dlg.getResult()) {
			if (o instanceof SVDBTaskFuncScope) {
				ret.add((SVDBTaskFuncScope)o);
			}
		}
		
		return ret;
	}
	
}
