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


package net.sf.sveditor.ui.pref;
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.ComboFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import net.sf.sveditor.ui.SVUiPlugin;

public class SVEditorPrefsPage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

	public SVEditorPrefsPage() {
		super(GRID);
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
		setDescription("Syntax Coloring");
	}

	public void createFieldEditors() {
		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_DEFAULT_C, "D&efault text color:", SVEditorPrefsConstants.P_DEFAULT_S, getFieldEditorParent()));
		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_COMMENT_C, "&Comment color:", SVEditorPrefsConstants.P_COMMENT_S, getFieldEditorParent()));
		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_STRING_C , "&String color:", SVEditorPrefsConstants.P_STRING_S, getFieldEditorParent()));
		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_KEYWORD_C, "Key&word color:", SVEditorPrefsConstants.P_KEYWORD_S, getFieldEditorParent()));
		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_NUMBERS_C, "N&umber color:", SVEditorPrefsConstants.P_NUMBERS_S, getFieldEditorParent()));
		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_OPERATORS_C, "&Operator color:", SVEditorPrefsConstants.P_OPERATORS_S, getFieldEditorParent()));
		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_SVT_PARAMETERS_S, "S&VT Template Parameter color:", 
				SVEditorPrefsConstants.P_SVT_PARAMETERS_S, getFieldEditorParent()));
		addField( new ColorStyleFieldEditor(SVEditorPrefsConstants.P_BRACE_C  , "B&racket color:", SVEditorPrefsConstants.P_BRACE_S, getFieldEditorParent()));
		addField( new ColorFieldEditor(SVEditorPrefsConstants.P_MATCHING_BRACE_C  , "&Matching Bracket color:", getFieldEditorParent()));
		
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_AUTO_INDENT_ENABLED_S, "Enable Auto-&Indent:", getFieldEditorParent()));

		addField( new ComboFieldEditor(SVEditorPrefsConstants.P_DEBUG_LEVEL_S, "Debug &Level:", 
				new String[][] {
					{"Off", "LEVEL_OFF"}, 
					{"Minimum", "LEVEL_MIN"}, 
					{"Medium", "LEVEL_MID"},
					{"Maximum", "LEVEL_MAX"}}, getFieldEditorParent()));
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_DEBUG_CONSOLE_S, 
				"Debu&g to Console:", getFieldEditorParent()));
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	public void init(IWorkbench workbench) {
	}
}
