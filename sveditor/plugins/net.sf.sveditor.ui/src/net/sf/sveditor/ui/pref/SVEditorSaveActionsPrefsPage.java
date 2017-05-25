/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.pref;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import net.sf.sveditor.ui.SVUiPlugin;

public class SVEditorSaveActionsPrefsPage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

	public SVEditorSaveActionsPrefsPage() {
		super(GRID);
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
	}

	public void createFieldEditors() {
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_REMOVE_TRAILING_WHITESPACE, "Remove trailing &whitespace", getFieldEditorParent()));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_NEWLINE_AT_END_OF_FILE, "Ensure &newline at the end of file", getFieldEditorParent()));
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	public void init(IWorkbench workbench) {
	}
}
