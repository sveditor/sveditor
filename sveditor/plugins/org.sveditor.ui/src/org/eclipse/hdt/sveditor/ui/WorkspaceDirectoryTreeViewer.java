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
package org.eclipse.hdt.sveditor.ui;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.model.WorkbenchContentProvider;
import org.eclipse.ui.model.WorkbenchLabelProvider;

public class WorkspaceDirectoryTreeViewer extends TreeViewer {
	
	public WorkspaceDirectoryTreeViewer(Composite parent, int style) {
		super(parent, style);

		setContentProvider(new WorkbenchContentProvider());
		addFilter(new ViewerFilter() {

			@Override
			public boolean select(Viewer viewer, Object parentElement,
					Object element) {
				return (element instanceof IContainer);
			}
		});
		setLabelProvider(new WorkbenchLabelProvider());
		setInput(ResourcesPlugin.getWorkspace());
	}
	
}
