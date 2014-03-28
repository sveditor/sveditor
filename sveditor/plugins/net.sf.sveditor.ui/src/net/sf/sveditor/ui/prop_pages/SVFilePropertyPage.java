/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.prop_pages;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.search.SVDBSearchResult;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.IWorkbenchPropertyPage;
import org.eclipse.ui.dialogs.PropertyPage;

public class SVFilePropertyPage extends PropertyPage implements
		IWorkbenchPropertyPage {

	public SVFilePropertyPage() {
	}

	@Override
	protected Control createContents(Composite parent) {
		StringBuilder index_info = new StringBuilder();
		IAdaptable adaptable = getElement();
		IFile file;
		Composite c = new Composite(parent, SWT.NONE);
		c.setLayout(new GridLayout());
		
		file = (IFile)adaptable.getAdapter(IFile.class);
		
		Label l = new Label(c, SWT.NONE);
		l.setText("Resource: " + file.getFullPath().toOSString());
		
		Group index_details_g = new Group(c, SWT.SHADOW_ETCHED_IN);
		index_details_g.setText("Index Details");
		index_details_g.setLayout(new GridLayout());
		index_details_g.setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		TextViewer index_details = new TextViewer(index_details_g, SWT.READ_ONLY);
		index_details.getControl().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));

		// Determine how indexing is handled for this file
		String file_path = "${workspace_loc}" + file.getFullPath().toOSString();
		
		file_path = SVFileUtils.normalize(file_path);
		
//		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		SVDBProjectManager mgr = SVCorePlugin.getDefault().getProjMgr();

		IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
		boolean found = false;
		for (IProject project : root.getProjects()) {
			SVDBProjectData proj_data = mgr.getProjectData(project);
			SVDBIndexCollection index_mgr = proj_data.getProjectIndexMgr();
			List<SVDBSearchResult<SVDBFile>> result = index_mgr.findPreProcFile(file_path, true);

			if (result.size() > 0) {
				ISVDBIndex index = result.get(0).getIndex(); 
				index_info.append("File \"" + file_path + "\" is in index " +
						index.getBaseLocation() + "\n");
				index_info.append("    Index Type: " + index.getClass().getName() + "\n");
				found = true;
			}
		}
		
		if (!found) {
			index_info.append("File \"" + file_path + "\" managed by a shadow index");
		}
		
		Document doc = new Document(index_info.toString());
		index_details.setDocument(doc);

		Dialog.applyDialogFont(c);
		
		return c;
	}

}
