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
import java.util.ResourceBundle;

import net.sf.sveditor.ui.editor.SVEditor;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.TextEditorAction;

public class OpenQuickObjectsViewAction extends TextEditorAction {
	
	private IWorkbench				fWorkbench;
	private SVEditor fEditor;
	
	public OpenQuickObjectsViewAction(
			ResourceBundle			bundle,
			SVEditor editor) {
		
		super(bundle, "OpenQuickObjects.", editor) ;
		
		fEditor = editor ;
		
		fWorkbench = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getWorkbench() ;
	}

	@Override
	public void run() {
		try {
			fWorkbench.getProgressService().run(false, false, fOpenQuickObjects);
		} catch (InvocationTargetException e) {
		} catch (InterruptedException e) {
		}
	}
	
	private IRunnableWithProgress fOpenQuickObjects = new IRunnableWithProgress() {
		
		public void run(IProgressMonitor monitor) throws InvocationTargetException,
				InterruptedException {
			
			monitor.beginTask("Open Objects View", 2);
			
			monitor.worked(1);
			
			fEditor.getQuickObjectsPresenter().showInformation() ;
			
			monitor.done();
		}
	};
	

}
