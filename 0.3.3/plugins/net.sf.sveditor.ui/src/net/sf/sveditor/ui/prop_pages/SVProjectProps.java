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


package net.sf.sveditor.ui.prop_pages;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.ui.IWorkbenchPropertyPage;
import org.eclipse.ui.dialogs.PropertyPage;

/**
 * 
 * @author ballance
 *
 */
public class SVProjectProps extends PropertyPage implements
		IWorkbenchPropertyPage {

	private List<ISVProjectPropsPage>	fPropertyPages;
	private SVDBProjectData				fProjectData;
	private SVProjectFileWrapper		fProjectFileWrapper;

	public SVProjectProps() {
		fPropertyPages = new ArrayList<ISVProjectPropsPage>();
		
		noDefaultAndApplyButton();
	}

	@Override
	protected Control createContents(Composite parent) {

		IProject p = getProject();
		
		SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();
		fProjectData = mgr.getProjectData(p);
		fProjectFileWrapper = fProjectData.getProjectFileWrapper().duplicate();
		
		// Create property pages
		fPropertyPages.add(new GlobalDefinesPage());
		fPropertyPages.add(new SourceCollectionsPage());
		// fPropertyPages.add(new IncludePathsPage());
		fPropertyPages.add(new LibraryPathsPage());
		fPropertyPages.add(new ArgumentFilePathsPage());
		fPropertyPages.add(new PluginLibPrefsPage());
		
		TabFolder folder = new TabFolder(parent, SWT.NONE);
		
		TabItem item;
		
		for (ISVProjectPropsPage page : fPropertyPages) {
			page.init(fProjectFileWrapper);
			
			item = new TabItem(folder, SWT.NONE);
			item.setText(page.getName());
			
			if (page.getIcon() != null) {
				item.setImage(page.getIcon());
			}
		
			item.setControl(page.createContents(folder));
		}
		
		Dialog.applyDialogFont(folder);
		
		return folder;
	}
	

	@Override
	public boolean performOk() {
		for (ISVProjectPropsPage page : fPropertyPages) {
			page.perfomOk();
		}
		
		fProjectData.setProjectFileWrapper(fProjectFileWrapper);
		
		return true;
	}

	private IProject getProject() {
		
		IAdaptable adaptable = getElement();
		if (adaptable != null) {
			IProject proj = (IProject)adaptable.getAdapter(IProject.class);
			
			return proj;
		}
		return null;
	}
	

}
