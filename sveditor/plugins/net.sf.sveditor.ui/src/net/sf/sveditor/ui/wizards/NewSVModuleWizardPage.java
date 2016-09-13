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


package net.sf.sveditor.ui.wizards;


import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

public class NewSVModuleWizardPage extends AbstractNewSVItemFileWizardPage {
	
	public NewSVModuleWizardPage(AbstractNewSVItemFileWizard parent) {
		super(parent, "New SystemVerilog Module", 
				"SystemVerilog Module", 
				"Create a new SystemVerilog module");
		fFileExt = ".sv";
	}
	
	@Override
	protected void createCustomContent(Composite src_c) {
		Composite c = new Composite(src_c, SWT.NONE);
		c.setLayout(new GridLayout(2, false));
		
		final Button b = new Button(c, SWT.CHECK);
		b.setText("&Create Verilog Module");
		b.addSelectionListener(new SelectionListener() {
			
			@Override
			public void widgetSelected(SelectionEvent e) {
				if (b.getSelection()) {
					fFileExt = ".v";
				} else {
					fFileExt = ".sv";
				}
				updateFilename();
			}
			
			@Override
			public void widgetDefaultSelected(SelectionEvent e) { }
		});
	}
}
