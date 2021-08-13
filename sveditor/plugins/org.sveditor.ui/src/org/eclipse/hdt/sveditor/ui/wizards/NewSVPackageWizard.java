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


package org.eclipse.hdt.sveditor.ui.wizards;

import org.eclipse.hdt.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.hdt.sveditor.core.srcgen.NewPackageGenerator;

public class NewSVPackageWizard extends AbstractNewSVItemFileWizard {
	public static final String				ID = SVUiPlugin.PLUGIN_ID + ".newSVPackageWizard";

	public NewSVPackageWizard() {
		super();
	}
	
	
	@Override
	protected AbstractNewSVItemFileWizardPage createPage() {
		return new NewSVPackageWizardPage(this);
	}

	@Override
	protected void generate(IProgressMonitor monitor, IFile file_path) {
		NewPackageGenerator gen = new NewPackageGenerator(fTagProc);
		SubMonitor subMonitor = SubMonitor.convert(monitor, 2);
		
		gen.generate(getIndexIterator(subMonitor.newChild(1)), 
				file_path,
				fPage.getOption(AbstractNewSVItemFileWizardPage.NAME, null),
				subMonitor.newChild(1));
	}

}
