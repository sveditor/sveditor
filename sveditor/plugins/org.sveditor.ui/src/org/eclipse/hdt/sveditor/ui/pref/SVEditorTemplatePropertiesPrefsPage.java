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
package org.sveditor.ui.pref;

import org.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

public class SVEditorTemplatePropertiesPrefsPage 
	extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
	
	public SVEditorTemplatePropertiesPrefsPage() {
		super(GRID);
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
//		setDescription("SystemVerilog Template Paths");
	}

	public void init(IWorkbench workbench) {
	}

	@Override
	protected void createFieldEditors() {
		TemplatePropertiesEditor ed = new TemplatePropertiesEditor(
				SVEditorPrefsConstants.P_SV_TEMPLATE_PROPERTIES, getFieldEditorParent());
		addField(ed);
	}
}
