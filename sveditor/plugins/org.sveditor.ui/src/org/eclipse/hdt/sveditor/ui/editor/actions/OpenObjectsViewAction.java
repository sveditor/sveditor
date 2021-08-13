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
 *     Armond Paiva - repurposed from hierarchy view to objects view
 ****************************************************************************/


package org.eclipse.hdt.sveditor.ui.editor.actions;

import java.lang.reflect.InvocationTargetException;
import java.util.ResourceBundle;

import org.eclipse.hdt.sveditor.ui.SVUiPlugin;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.ResourceAction;

public class OpenObjectsViewAction extends ResourceAction {
	
	private IWorkbench				fWorkbench;
	
	public OpenObjectsViewAction(
			ResourceBundle			bundle) {
		super(bundle, "OpenObjects.") ;
		
		fWorkbench = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getWorkbench() ;
	}

	@Override
	public void run() {
		try {
			fWorkbench.getProgressService().run(false, false, fOpenObjects);
		} catch (InvocationTargetException e) {
		} catch (InterruptedException e) {
		}
	}
	
	private IRunnableWithProgress fOpenObjects = new IRunnableWithProgress() {
		
		public void run(IProgressMonitor monitor) throws InvocationTargetException,
				InterruptedException {
			
			monitor.beginTask("Open Objects View", 2);
			
			monitor.worked(1);
			
			try {
				IWorkbench workbench = PlatformUI.getWorkbench();
				IWorkbenchPage page = workbench.getActiveWorkbenchWindow().getActivePage();
				IViewPart view;
				if ((view = page.findView(SVUiPlugin.PLUGIN_ID + ".objectsView")) == null) {
					view = page.showView(SVUiPlugin.PLUGIN_ID + ".objectsView");
				}

				page.activate(view);

			} catch (Exception e) {
				e.printStackTrace();
			}			
			
			monitor.done();
		}
	};
	

}
