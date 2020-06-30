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

import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Label;

public class ColorStyleFieldEditor extends ColorFieldEditor {
	protected Button [] checkButton;
	static private String [] styleText = new String [] {"Bold", "Italic"};
	static private String labelText = "Style:";
	private String stylePreference;
	private Label styleLabel;

	public ColorStyleFieldEditor() {
		super();
	}

	public ColorStyleFieldEditor(String name, String labelText, String stylePref, Composite parent) {
		super(name, labelText, parent);
		this.stylePreference = stylePref;
	}
	
	protected void doFillIntoGrid(Composite parent, int numColumns) {
		Control control = getLabelControl(parent);
		GridData gd = new GridData();
		gd.horizontalSpan = numColumns - 4;
		control.setLayoutData(gd);

		Button colorButton = getChangeControl(parent);
		colorButton.setLayoutData(new GridData());
		
		Label lb = getStyleLabel(parent);
		lb.setLayoutData(new GridData());
		
		for (int i = 0; i < 2; i++) {
			Button checkButton = getCheckButton(parent, i);
			checkButton.setLayoutData(new GridData());
		}
		
	}
	
	protected void adjustForNumColumns(int numColumns) {
		((GridData) styleLabel.getLayoutData()).horizontalSpan = 1;
		for (int i = 0; i < 2; i++) {
			((GridData) checkButton[i].getLayoutData()).horizontalSpan = 1;
		}
	}
	
	protected Button getCheckButton(Composite parent, int i) {
		if (checkButton == null) checkButton = new Button [2];
		if(checkButton[i] != null) return(checkButton[i]);
		else {
			checkButton[i] = new Button(parent, SWT.CHECK);
			if(checkButton[i] != null) checkButton[i].setText(styleText[i]);
			return(checkButton[i]);
		}
	}
	protected Label getStyleLabel(Composite parent) {
		if (styleLabel != null) return (styleLabel);
		else {
			styleLabel = new Label(parent, SWT.LEFT);
			if(styleLabel != null) styleLabel.setText(labelText);
			return (styleLabel);
		}
	}
	
	protected void doLoad() {
		super.doLoad();
		if (checkButton[0] == null) return;
		checkButton[0].setSelection((getPreferenceStore().getInt(stylePreference) == SWT.BOLD) | 
									(getPreferenceStore().getInt(stylePreference) == (SWT.BOLD|SWT.ITALIC)) ? true : false );
		if (checkButton[1] == null) return;
		checkButton[1].setSelection((getPreferenceStore().getInt(stylePreference) == SWT.ITALIC) | 
									(getPreferenceStore().getInt(stylePreference) == (SWT.BOLD|SWT.ITALIC)) ? true : false );
		
	}

	protected void doLoadDefault() {
		super.doLoadDefault();
		if (checkButton[0] == null) return;
		checkButton[0].setSelection((getPreferenceStore().getDefaultInt(stylePreference) == SWT.BOLD) | 
									(getPreferenceStore().getDefaultInt(stylePreference) == (SWT.BOLD|SWT.ITALIC)) ? true : false );
		if (checkButton[1] == null) return;
		checkButton[1].setSelection((getPreferenceStore().getDefaultInt(stylePreference) == SWT.ITALIC) | 
									(getPreferenceStore().getDefaultInt(stylePreference) == (SWT.BOLD|SWT.ITALIC)) ? true : false );
	}

	protected void doStore() {
		super.doStore();
		getPreferenceStore().setValue(stylePreference, 
				 (checkButton[0].getSelection() ? SWT.BOLD : SWT.NORMAL) |								
				 (checkButton[1].getSelection() ? SWT.ITALIC : SWT.NORMAL));
	}

	public int getNumberOfControls() {
		return super.getNumberOfControls() + 3;
	}

	public void setEnabled(boolean enabled, Composite parent) {
		super.setEnabled(enabled, parent);
		for (int i = 0; i < 2; i++)
			checkButton[i].setEnabled(enabled);
	}

}
