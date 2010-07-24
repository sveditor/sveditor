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

import java.lang.reflect.InvocationTargetException;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.srcgen.NewClassGenerator;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

public class NewSVClassWizard extends BasicNewResourceWizard {
	public static final String				ID = SVUiPlugin.PLUGIN_ID + ".newSVClassWizard";
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
		IContainer c = SVFileUtils.getWorkspaceFolder(fPage.getSourceFolder());
		final IFile file_path = c.getFile(new Path(fPage.getFileName()));
		
		ISVDBIndexIterator index_it = null;
		if (fPage.getProjectData() != null) {
			index_it = fPage.getProjectData().getProjectIndexMgr();
		}
		final ISVDBIndexIterator index_it_f = index_it;
		
		IRunnableWithProgress op = new IRunnableWithProgress() {
			public void run(IProgressMonitor monitor) throws InvocationTargetException,
					InterruptedException {
				NewClassGenerator gen = new NewClassGenerator();
				gen.generate(index_it_f, file_path, fPage.getName(), 
						fPage.getSuperClass(), fPage.getOverrideNew(), monitor);
			}
		};
		
		try {
			getContainer().run(false, false, op);
		} catch (Exception e) {
			return false;
		}
		
		SVEditorUtil.openEditor("${workspace_loc}/" + file_path.getFullPath());

		return true;
	}


}
