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


package org.sveditor.ui.wizards;


import org.eclipse.swt.widgets.Composite;

public class NewSVInterfaceWizardPage extends AbstractNewSVItemFileWizardPage {
	
	public NewSVInterfaceWizardPage(AbstractNewSVItemFileWizard parent) {
		super(parent, "New SystemVerilog Interface", 
				"SystemVerilog Interface", 
				"Create a new SystemVerilog interface");
		fFileExt = ".sv";
	}
	
	@Override
	protected void createCustomContent(Composite src_c) {
	}

}
