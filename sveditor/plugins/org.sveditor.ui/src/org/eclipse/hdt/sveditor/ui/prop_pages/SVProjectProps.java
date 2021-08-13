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


package org.eclipse.hdt.sveditor.ui.prop_pages;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.SVProjectNature;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;
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
//		fPropertyPages.add(new SourceCollectionsPage(p));
		// fPropertyPages.add(new IncludePathsPage(p));
//		fPropertyPages.add(new LibraryPathsPage(p));
		fPropertyPages.add(new ArgumentFilePathsPage(p));
//		fPropertyPages.add(new GlobalDefinesPage(p));
		fPropertyPages.add(new TemplatePathsPage(p));
		fPropertyPages.add(new PluginLibPrefsPage());
//		fPropertyPages.add(new DeprecatedPropertiesPage(p));
		
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

		// Ensure this project is tagged as an SVE project
		SVProjectNature.ensureHasSvProjectNature(getProject());
		
		fProjectData.setProjectFileWrapper(fProjectFileWrapper);
	
		// Don't need to do this
//		fProjectData.getProjectIndexMgr().rebuildIndex(new NullProgressMonitor());
		
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
