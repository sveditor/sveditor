/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.ui.prop_pages;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.project.SVProjectFileWrapper;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;

public class DeprecatedPropertiesPage implements ISVProjectPropsPage {
	private List<ISVProjectPropsPage>			fSubPages;
	private IProject							fProject;
	private SVProjectFileWrapper				fProjectWrapper;
	
	public DeprecatedPropertiesPage(IProject p) {
		fSubPages = new ArrayList<ISVProjectPropsPage>();
		fProject = p;
	}

	public String getName() {
		return "Deprecated";
	}

	public Image getIcon() {
		return null;
	}

	public void init(SVProjectFileWrapper project_wrapper) {
		fProjectWrapper = project_wrapper;
	}

	public Control createContents(Composite parent) {
		fSubPages.add(new GlobalDefinesPage(fProject));
		fSubPages.add(new SourceCollectionsPage(fProject));
		fSubPages.add(new LibraryPathsPage(fProject));
		
		TabFolder folder = new TabFolder(parent, SWT.NONE);
		TabItem item;
		
		for (ISVProjectPropsPage p : fSubPages) {
			p.init(fProjectWrapper);
			
			item = new TabItem(folder, SWT.NONE);
			item.setText(p.getName());
			
			if (p.getIcon() != null) {
				item.setImage(p.getIcon());
			}
			
			item.setControl(p.createContents(folder));
		}
		
		Dialog.applyDialogFont(folder);

		return folder;
	}

	public void perfomOk() {
		for (ISVProjectPropsPage p : fSubPages) {
			p.perfomOk();
		}
	}
}
