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
package org.eclipse.hdt.sveditor.ui.pref;

import org.eclipse.hdt.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

public class SVEditorFoldingPrefsPage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
	
	public SVEditorFoldingPrefsPage() {
		super(GRID);
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
		setDescription("Folding");
	}

	public void init(IWorkbench workbench) {
		// TODO Auto-generated method stub
		
	}

	@Override
	protected void createFieldEditors() {
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_ENABLE, 
				"&Enable folding when opening a new editor", getFieldEditorParent()));
		
		Group g = new Group(getFieldEditorParent(), SWT.NONE);
		g.setText("Initially fold these regions");
		
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_INIT_CLASSES, 
				"&Classes", g));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_INIT_INTERFACES, 
				"&Interfaces", g));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_INIT_MODULES, 
				"&Modules", g));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_INIT_TF, 
				"&Tasks/Functions", g));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_INIT_UNPROCESSED, 
				"&Unprocessed Regions", g));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_INIT_HEADER_COMMENTS, 
				"&Header Comments", g));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_FOLDING_INIT_BLOCK_COMMENTS,
				"&Block Comments", g));
		
	}

}
