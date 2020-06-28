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
package net.sf.sveditor.ui.pref;

import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditorPreferencePage;
import org.eclipse.jface.preference.IntegerFieldEditor;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.widgets.Button;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPreferencePage;

public class SVEditorIndexPrefsPage extends FieldEditorPreferencePage implements IWorkbenchPreferencePage {
	private BooleanFieldEditor			fEditorAutoIndexEn;
	private IntegerFieldEditor			fEditorAutoIndexDelay;
	
	public SVEditorIndexPrefsPage() {
		super(GRID);
		setPreferenceStore(SVUiPlugin.getDefault().getPreferenceStore());
		setDescription("Index Preferences");
	}

	public void init(IWorkbench workbench) {
		// TODO Auto-generated method stub
		
	}

	@Override
	protected void createFieldEditors() {
		addField( new BooleanFieldEditor(SVEditorPrefsConstants.P_OVERRIDE_FILE_EXTENSION_LANGUAGE_LEVEL, 
				"&Override Language Level based on file extension. Treat all source as SystemVerilog", 
				getFieldEditorParent()));
		
		fEditorAutoIndexEn = new BooleanFieldEditor(
				SVEditorPrefsConstants.P_EDITOR_AUTOINDEX_ENABLE,
				"&Enable Editor Auto-Index", getFieldEditorParent());
		addField(fEditorAutoIndexEn);
		
		fEditorAutoIndexDelay = new IntegerFieldEditor(
				SVEditorPrefsConstants.P_EDITOR_AUTOINDEX_DELAY, 
				"Ed&itor Auto-Index Delay (mS):", getFieldEditorParent());
		fEditorAutoIndexDelay.setValidRange(0, Integer.MAX_VALUE);
		addField(fEditorAutoIndexDelay);
	}

	@Override
	protected void initialize() {
		super.initialize();
		fEditorAutoIndexDelay.setEnabled(
				fEditorAutoIndexEn.getBooleanValue(),
				getFieldEditorParent());
	
		final Button b = (Button)fEditorAutoIndexEn.getDescriptionControl(
				getFieldEditorParent());
		b.addSelectionListener(new SelectionListener() {
			
			@Override
			public void widgetSelected(SelectionEvent e) {
				fEditorAutoIndexDelay.setEnabled(
						b.getSelection(),
						getFieldEditorParent());
			}
			
			@Override
			public void widgetDefaultSelected(SelectionEvent e) { }
		});
	}

	@Override
	protected void performDefaults() {
		// TODO Auto-generated method stub
		super.performDefaults();
	}
	
}
