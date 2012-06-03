/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 *     Armond Paiva - repurposed from hierarchy view to objects view
 ****************************************************************************/


package net.sf.sveditor.ui.editor.actions;

import java.lang.reflect.InvocationTargetException;
import java.util.List;
import java.util.ResourceBundle;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.objects.ObjectsTreeFactory;
import net.sf.sveditor.core.objects.ObjectsTreeNode;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.views.objects.SVObjectsView;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IURIEditorInput;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.TextEditorAction;

public class OpenObjectsViewAction extends TextEditorAction {
	
	private IWorkbench				fWorkbench;
	
	public OpenObjectsViewAction(
			ResourceBundle			bundle,
			SVEditor				editor) {
		
		super(bundle, "OpenObjects.", editor);
		fWorkbench = editor.getEditorSite().getWorkbenchWindow().getWorkbench();
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
			
			monitor.beginTask("Open Objects View", 4);
			
			monitor.worked(1);
			
			List<ISVDBIndex> projectIndexList = null ;
			
			IEditorInput ed_in = getTextEditor().getEditorInput() ;
			
			if (ed_in instanceof IURIEditorInput) {
				
				SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
				
				if (ed_in instanceof FileEditorInput) {
					FileEditorInput fi = (FileEditorInput)ed_in ;
					IProject proj = fi.getFile().getProject() ;
					projectIndexList = rgy.getProjectIndexList(proj.getName()) ;
				}
				
			}
			
				
			ObjectsTreeNode n = null ;
			
			if(projectIndexList != null) {
			
				ObjectsTreeFactory factory = new ObjectsTreeFactory(projectIndexList) ;
				n = factory.build() ; 
			}
			
			if(n != null) {
				try {
					IWorkbench workbench = PlatformUI.getWorkbench();
					IWorkbenchPage page = workbench.getActiveWorkbenchWindow().getActivePage();
					IViewPart view;
					if ((view = page.findView(SVUiPlugin.PLUGIN_ID + ".objectsView")) == null) {
						view = page.showView(SVUiPlugin.PLUGIN_ID + ".objectsView");
					}
	
					page.activate(view);
	
					((SVObjectsView)view).setTarget(n);
	
				} catch (Exception e) {
					e.printStackTrace();
				}			
				
			}
			
			monitor.done();
		}
	};
	

}
