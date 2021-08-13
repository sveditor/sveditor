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
import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

import org.eclipse.hdt.sveditor.ui.SVUiPlugin;

public class SVEditorSaveActionsPrefsPage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {

	private BooleanFieldEditor fPerformActionsOnSave;
	private BooleanFieldEditor fRemoveTrailingWhitespace;
	private BooleanFieldEditor fNewlineAtEndOfFile;
	private BooleanFieldEditor fFormatSourceCode;
	
	public SVEditorSaveActionsPrefsPage() {
		super(GRID);
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
	}

	public void createFieldEditors() {
		fPerformActionsOnSave     = new BooleanFieldEditor(SVEditorPrefsConstants.P_PERFORM_ACTIONS_ON_SAVE, "Per&form the selected actions on save", getFieldEditorParent());
		fRemoveTrailingWhitespace = new BooleanFieldEditor(SVEditorPrefsConstants.P_REMOVE_TRAILING_WHITESPACE, "Remove trailing &whitespace", getFieldEditorParent());
		fNewlineAtEndOfFile       = new BooleanFieldEditor(SVEditorPrefsConstants.P_NEWLINE_AT_END_OF_FILE, "Ensure &newline at the end of file", getFieldEditorParent());
		fFormatSourceCode         = new BooleanFieldEditor(SVEditorPrefsConstants.P_FORMAT_SOURCE_CODE, "Format &source code", getFieldEditorParent());

		addField( fPerformActionsOnSave );
		addField( fRemoveTrailingWhitespace );
		addField( fNewlineAtEndOfFile );
		addField( fFormatSourceCode );
		
		// Initialize various odds and ends
		initialize();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IWorkbenchPreferencePage#init(org.eclipse.ui.IWorkbench)
	 */
	public void init(IWorkbench workbench) {
	}
	
	
	protected void initialize()  {
		super.initialize();
		
		fPerformActionsOnSave.setPropertyChangeListener((IPropertyChangeListener) new MyPropertyChangeListener(this));

		// Check whether we should grey out some of these items based on the PerformActionOnSave
		fRemoveTrailingWhitespace.setEnabled(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_PERFORM_ACTIONS_ON_SAVE), getFieldEditorParent());
		fNewlineAtEndOfFile      .setEnabled(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_PERFORM_ACTIONS_ON_SAVE), getFieldEditorParent());
		fFormatSourceCode        .setEnabled(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_PERFORM_ACTIONS_ON_SAVE), getFieldEditorParent());
	}
	
	private class MyPropertyChangeListener implements IPropertyChangeListener{

		private FieldEditorPreferencePage page;

		public MyPropertyChangeListener(FieldEditorPreferencePage nodePreferencePage) {
			page = nodePreferencePage;
		}

		@Override
		public void propertyChange(PropertyChangeEvent event) {
			page.propertyChange(event);
			// Check whether we should grey out some of these items based on the PerformActionOnSave
			fRemoveTrailingWhitespace.setEnabled((Boolean) event.getNewValue(), getFieldEditorParent());
			fNewlineAtEndOfFile      .setEnabled((Boolean) event.getNewValue(), getFieldEditorParent());
			fFormatSourceCode        .setEnabled((Boolean) event.getNewValue(), getFieldEditorParent());
		}
	}
}
