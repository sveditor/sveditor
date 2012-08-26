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
import net.sf.sveditor.ui.SVEditorUtil;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

abstract public class AbstractNewSVItemFileWizard extends BasicNewResourceWizard {
//	public static final String				ID = SVUiPlugin.PLUGIN_ID + ".newSVClassWizard";
	protected AbstractNewSVItemFileWizardPage		fPage;

	public AbstractNewSVItemFileWizard() {
		super();
	}
	
	abstract protected AbstractNewSVItemFileWizardPage createPage();
	
	abstract protected void generate(IProgressMonitor monitor, IFile file_path);
	
	public void addPages() {
		super.addPages();
		
		fPage = createPage();
		Object sel = getSelection().getFirstElement();
		if (sel != null && sel instanceof IResource) {
			IResource r = (IResource)sel;
			
			if (!(r instanceof IContainer)) {
				r = r.getParent();
			}
			fPage.setOption(AbstractNewSVItemFileWizardPage.SOURCE_FOLDER,
					r.getFullPath().toOSString());
		}
		addPage(fPage);
	}

	public void init(IWorkbench workbench, IStructuredSelection selection) {
		super.init(workbench, selection);
		setNeedsProgressMonitor(true);
	}
	
	protected ISVDBIndexIterator getIndexIterator(IProgressMonitor monitor) {
		ISVDBIndexIterator index_it = null;
		if (fPage.getProjectData() != null) {
			index_it = fPage.getProjectData().getProjectIndexMgr();
		}

		return index_it;
	}

	@Override
	public boolean performFinish() {
		IContainer c = SVFileUtils.getWorkspaceFolder(
				fPage.getOption(AbstractNewSVItemFileWizardPage.SOURCE_FOLDER, null));
		final IFile file_path = c.getFile(new Path(
				fPage.getOption(AbstractNewSVItemFileWizardPage.FILE_NAME, null)));
		
		IRunnableWithProgress op = new IRunnableWithProgress() {
			public void run(IProgressMonitor monitor) throws InvocationTargetException,
					InterruptedException {
				generate(monitor, file_path);
			}
		};
		
		try {
			getContainer().run(false, false, op);
		} catch (Exception e) {
			return false;
		}
		
		try {
			SVEditorUtil.openEditor("${workspace_loc}/" + file_path.getFullPath());
		} catch (PartInitException e) {
			e.printStackTrace();
		}

		return true;
	}


}
