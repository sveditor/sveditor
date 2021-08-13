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


package org.eclipse.hdt.sveditor.ui.pref;

import org.eclipse.hdt.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Group;
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
		GridData gd;
		
		Group general_group = new Group(getFieldEditorParent(), SWT.NONE);
		gd = new GridData(GridData.FILL, GridData.CENTER, true, false);
		gd.horizontalSpan = 2;
		general_group.setLayout(new GridLayout(2, false));
		general_group.setLayoutData(gd);
		general_group.setText("General");
		addField(new IntegerFieldEditor(SVEditorPrefsConstants.P_CONTENT_ASSIST_TIMEOUT, 
				"&Content Assist Timeout (ms)", general_group));
		/** No value in preserving this for users to play with. 
		addField(new BooleanFieldEditor(SVEditorPrefsConstants.P_CONTENT_ASSIST_HOVER_USES_BROWSER, 
				"&Hover Uses Browser:", general_group));
		 */

		
		Group tf_group = new Group(getFieldEditorParent(), SWT.NONE);
		gd = new GridData(GridData.FILL, GridData.CENTER, true, false);
		gd.horizontalSpan = 2;
		tf_group.setLayout(new GridLayout(2, false));
		tf_group.setText("Task/Function Settings");
		tf_group.setLayoutData(gd);
		addField(new BooleanFieldEditor(SVEditorPrefsConstants.P_CONTENT_ASSIST_TF_NAMED_PORTS_EN, 
				"&Enable Named Parameters:", tf_group));
		addField(new IntegerFieldEditor(SVEditorPrefsConstants.P_CONTENT_ASSIST_TF_LINE_WRAP_LIMIT, 
				"&Line-Wrap Limit: ", tf_group));
		addField(new IntegerFieldEditor(SVEditorPrefsConstants.P_CONTENT_ASSIST_TF_MAX_PARAMS_PER_LINE, 
				"&Max Parameters Per Line:", tf_group));
		
		Group mod_ifc_group = new Group(getFieldEditorParent(), SWT.NONE);
		gd = new GridData(GridData.FILL, GridData.CENTER, true, false);
		gd.horizontalSpan = 2;
		mod_ifc_group.setLayout(new GridLayout(2, false));
		mod_ifc_group.setText("Module/Interface Settings");
		mod_ifc_group.setLayoutData(gd);
		addField(new BooleanFieldEditor(SVEditorPrefsConstants.P_CONTENT_ASSIST_MODIFCINST_NAMED_PORTS_EN, 
				"E&nable Named Port Map:", mod_ifc_group));
		addField(new IntegerFieldEditor(SVEditorPrefsConstants.P_CONTENT_ASSIST_MODIFCINST_LINE_WRAP_LIMIT, 
				"L&ine-Wrap Limit: ", mod_ifc_group));
		addField(new IntegerFieldEditor(SVEditorPrefsConstants.P_CONTENT_ASSIST_MODIFCINST_MAX_PORTS_PER_LINE, 
				"Max &Ports Per Line:", mod_ifc_group));
		
	}

}
