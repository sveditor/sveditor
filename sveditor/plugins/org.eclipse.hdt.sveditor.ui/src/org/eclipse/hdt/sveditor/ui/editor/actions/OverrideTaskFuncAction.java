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

import java.util.ArrayList;
import java.util.List;
import java.util.ResourceBundle;

import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.hdt.sveditor.core.db.ISVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBTask;
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

	public List<SVDBTask> getTargets(ISVDBScopeItem active_scope) {
		OverrideMethodsDialog dlg = null;
		
		try {
			dlg = new OverrideMethodsDialog(
					fEditor.getSite().getShell(),
					(SVDBClassDecl)active_scope, 
					fEditor.getIndexIterator());
		} catch (Exception e) {
			e.printStackTrace();
			return null;
		}

		dlg.setBlockOnOpen(true);
		
		dlg.open();
		
		if (dlg.getResult() == null) {
			return null;
		}
		
		List<SVDBTask> ret = new ArrayList<SVDBTask>();
		for (Object o : dlg.getResult()) {
			if (o instanceof SVDBTask) {
				ret.add((SVDBTask)o);
			}
		}
		
		return ret;
	}
	
}
