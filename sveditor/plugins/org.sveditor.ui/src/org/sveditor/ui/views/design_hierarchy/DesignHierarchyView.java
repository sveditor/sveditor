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
package org.sveditor.ui.views.design_hierarchy;

import org.sveditor.ui.SVEditorUtil;
import org.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.design_hierarchy.DesignHierarchyNode;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;

public class DesignHierarchyView extends ViewPart {
	private TreeViewer							fTreeViewer;
	private DesignHierarchyContentProvider		fContentProvider;
	private DesignHierarchyLabelProvider		fLabelProvider;
	private Action								fRefreshAction;
	private boolean								fRefreshJobRunning;
	
	@Override
	public void init(IViewSite site) throws PartInitException {
		super.init(site);
		
		IActionBars action_bars = site.getActionBars();
		
		fRefreshAction = new Action("Refresh", Action.AS_PUSH_BUTTON) {
			public void run() {
				fTreeViewer.refresh();
				synchronized (this) {
					if (!fRefreshJobRunning) {
						setRefreshJobRunning(true);
						refreshJob.schedule();
					}
				}
			}
		};
		fRefreshAction.setImageDescriptor(SVUiPlugin.getImageDescriptor("/icons/elcl16/refresh.gif"));
		action_bars.getToolBarManager().add(fRefreshAction);
	}

	private Job					refreshJob = new Job("Design Hierarchy Refresh") {
		
		@Override
		protected IStatus run(IProgressMonitor monitor) {
			try {
				fContentProvider.build(monitor);
				Display.getDefault().asyncExec(refreshViewer);
			} finally {
				setRefreshJobRunning(false);
			}
			return Status.OK_STATUS;
		}
	};
	
	private Runnable			refreshViewer = new Runnable() {
		@Override
		public void run() {
			fTreeViewer.refresh();
		}
	};
	
	private synchronized void setRefreshJobRunning(boolean running) {
		fRefreshJobRunning = running;
	}
	
	@Override
	public void createPartControl(Composite parent) {
		fTreeViewer = new TreeViewer(parent);
		fTreeViewer.getTree().setLayoutData(new GridData(SWT.FILL, SWT.FILL, true, true));
		
		fContentProvider = new DesignHierarchyContentProvider();
		fLabelProvider = new DesignHierarchyLabelProvider();
		
		fTreeViewer.setContentProvider(fContentProvider);
		fTreeViewer.setLabelProvider(fLabelProvider);
		
		fTreeViewer.addDoubleClickListener(doubleClickListener);
		fTreeViewer.setComparator(comparator);
		
		fTreeViewer.setInput(ResourcesPlugin.getWorkspace().getRoot());
	}
	
	private IDoubleClickListener doubleClickListener = new IDoubleClickListener() {
		
		@Override
		public void doubleClick(DoubleClickEvent event) {
			IStructuredSelection sel = (IStructuredSelection)fTreeViewer.getSelection();
			
			if (sel.getFirstElement() != null) {
				Object sel_o = sel.getFirstElement();
				
				if (sel_o instanceof DesignHierarchyNode) {
					DesignHierarchyNode dn = (DesignHierarchyNode)sel_o;
					Object target = dn.getTarget();
					
					if (target instanceof ISVDBItemBase) {
						try {
							SVEditorUtil.openEditor((ISVDBItemBase)target);
						} catch (PartInitException e) {
						}
					}
				}
			}
		}
	};
	
	private ViewerComparator comparator = new ViewerComparator() {

		@Override
		public int compare(Viewer viewer, Object e1, Object e2) {
			String n1 = fLabelProvider.getName(e1);
			String n2 = fLabelProvider.getName(e2);
			
			return n1.toLowerCase().compareTo(n2.toLowerCase());
		}
	};

	@Override
	public void setFocus() {
		// TODO Auto-generated method stub

	}

}
