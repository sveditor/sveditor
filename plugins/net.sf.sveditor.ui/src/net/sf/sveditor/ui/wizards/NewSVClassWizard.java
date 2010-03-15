/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.wizards;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

public class NewSVClassWizard extends BasicNewResourceWizard {
	private NewSVClassWizardPage			fPage;

	public NewSVClassWizard() {
		super();
	}
	
	public void addPages() {
		super.addPages();
		
		fPage = new NewSVClassWizardPage();
		Object sel = getSelection().getFirstElement();
		if (sel != null && sel instanceof IResource) {
			IResource r = (IResource)sel;
			
			if (!(r instanceof IContainer)) {
				r = r.getParent();
			}
			fPage.setSourceFolder(r.getFullPath().toOSString());
		}
		addPage(fPage);
	}

	public void init(IWorkbench workbench, IStructuredSelection selection) {
		super.init(workbench, selection);
		setNeedsProgressMonitor(true);
	}

	@Override
	public boolean performFinish() {
		return true;
	}


}
