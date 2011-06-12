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

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

public class NewSVMethodologyClassWizard extends BasicNewResourceWizard {
	public static final String					ID = SVUiPlugin.PLUGIN_ID + ".svMethodologyClass";
	private NewSVMethodologyClassWizardBasicsPage		fBasicsPage;
	private ISVSubWizard								fSubWizard;
	private Map<String, Object>							fOptions;

	public NewSVMethodologyClassWizard() {
		super();
		fOptions = new HashMap<String, Object>();
	}
	
	public void addPages() {
		super.addPages();
		
		fBasicsPage = new NewSVMethodologyClassWizardBasicsPage();
		
		Object sel = getSelection().getFirstElement();
		if (sel != null && sel instanceof IResource) {
			IResource r = (IResource)sel;
			
			if (!(r instanceof IContainer)) {
				r = r.getParent();
			}
			fBasicsPage.setSourceFolder(r.getFullPath().toOSString());
		}
		addPage(fBasicsPage);
	}
	
	@Override
	public boolean canFinish() {
		if (fSubWizard != null) {
			return fSubWizard.canFinish();
		} else {
			return super.canFinish();
		}
	}
	
	@Override
	public IWizardPage getNextPage(IWizardPage page) {
		if (fSubWizard != null) {
			return fSubWizard.getNextPage(page);
		} else {
			return super.getNextPage(page);
		}
	}
	
	@Override
	public IWizardPage getPreviousPage(IWizardPage page) {
		if (fSubWizard != null) {
			return fSubWizard.getPreviousPage(page);
		} else {
			return super.getPreviousPage(page);
		}
	}
	
	public void setSubWizard(ISVSubWizard sub) {
		fSubWizard = sub;
		if (fSubWizard != null) {
			fSubWizard.init(this, fOptions);
		}
	}

	public void init(IWorkbench workbench, IStructuredSelection selection) {
		super.init(workbench, selection);
		setNeedsProgressMonitor(true);
	}

	@Override
	public boolean performFinish() {
		IContainer c = SVFileUtils.getWorkspaceFolder(fBasicsPage.getSourceFolder());
		final IFile file_path = c.getFile(new Path(fBasicsPage.getFileName()));
		
		/*
		ISVDBIndexIterator index_it = null;
		if (fBasicsPage.getProjectData() != null) {
			index_it = fBasicsPage.getProjectData().getProjectIndexMgr();
		}
		final ISVDBIndexIterator index_it_f = index_it;
		 */
		
		/*
		IRunnableWithProgress op = new IRunnableWithProgress() {
			public void run(IProgressMonitor monitor) throws InvocationTargetException,
					InterruptedException {
				NewClassGenerator gen = new NewClassGenerator();
				gen.generate(index_it_f, file_path, fBasicsPage.getName(), 
						fBasicsPage.getSuperClass(), fBasicsPage.getOverrideNew(), monitor);
			}
		};
		
		try {
			getContainer().run(false, false, op);
		} catch (Exception e) {
			return false;
		}
		 */
		
		try {
			SVEditorUtil.openEditor("${workspace_loc}/" + file_path.getFullPath());
		} catch (PartInitException e) {
			e.printStackTrace();
		}

		return true;
	}


}
