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


package net.sf.sveditor.ui.wizards;


import org.eclipse.swt.widgets.Composite;

public class NewSVPackageWizardPage extends AbstractNewSVItemFileWizardPage {
	
	public NewSVPackageWizardPage(AbstractNewSVItemFileWizard parent) {
		super(parent, "New SystemVerilog Package", 
				"SystemVerilog Package", 
				"Create a new SystemVerilog package");
		fFileExt = ".sv";
	}
	
	@Override
	protected void createCustomContent(Composite src_c) {
	}

}
