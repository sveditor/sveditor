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


package net.sf.sveditor.ui.pref;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;



public class SVContentAssistPrefsPage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
	
	public SVContentAssistPrefsPage() {
		super(GRID);
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
		setDescription("Content Assist");
	}

    public void init(IWorkbench workbench) {
	}

	@Override
	protected void createFieldEditors() {
		addField(new BooleanFieldEditor(SVEditorPrefsConstants.P_CONTENT_ASSIST_NAMED_PORTS_EN, 
				"Enable Named Task/Function Parameters:", getFieldEditorParent()));
		addField(new IntegerFieldEditor(SVEditorPrefsConstants.P_CONTENT_ASSIST_LINE_WRAP_LIMIT, 
				"Content Assist Line-Wrap Limit: ", getFieldEditorParent()));
		addField(new IntegerFieldEditor(SVEditorPrefsConstants.P_CONTENT_ASSIST_TF_MAX_PARAMS_PER_LINE, 
				"Max Task/Function Parameters Per Line:", getFieldEditorParent()));
	}

}
