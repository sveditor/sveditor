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
 *     Armond Paiva - repurposed from hierarchy to diagram view
 ****************************************************************************/


package net.sf.sveditor.ui.editor.actions;

import java.lang.reflect.InvocationTargetException;
import java.util.ResourceBundle;

import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.views.diagram.SVDiagramView;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBModuleDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBPackageDecl;
import org.eclipse.hdt.sveditor.core.diagrams.ClassDiagModelFactory;
import org.eclipse.hdt.sveditor.core.diagrams.DiagModel;
import org.eclipse.hdt.sveditor.core.diagrams.IDiagModelFactory;
import org.eclipse.hdt.sveditor.core.diagrams.ModuleDiagModelFactory;
import org.eclipse.hdt.sveditor.core.diagrams.PackageClassDiagModelFactory;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.texteditor.TextEditorAction;

public class OpenDiagForSelectionAction extends TextEditorAction {
	
	private IWorkbench fWorkbench ;
	private SVEditor fEditor ;
	
	public OpenDiagForSelectionAction(
			ResourceBundle bundle,
			SVEditor editor) {
		
		super(bundle, "OpenDiagForSelection.", editor) ;
		
		fEditor = editor ;
		
		fWorkbench = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getWorkbench() ;
	}

	@Override
	public void run() {
		try {
			fWorkbench.getProgressService().run(false, false, fOpenDiagForSelection);
		} catch (InvocationTargetException e) {
		} catch (InterruptedException e) {
		}
	}
	
	private IRunnableWithProgress fOpenDiagForSelection = new IRunnableWithProgress() {
		
		public void run(IProgressMonitor monitor) throws InvocationTargetException,
				InterruptedException {
			
			monitor.beginTask("Open diag for selection", 2);
			
			monitor.worked(1);
			
			ISVDBItemBase itemBase = SelectionConverter.getElementAtOffset(fEditor) ;
			
			if(itemBase != null && (itemBase.getType() == SVDBItemType.ClassDecl ||
									itemBase.getType() == SVDBItemType.PackageDecl ||
									itemBase.getType() == SVDBItemType.ModuleDecl)) {
			
				try {
					IWorkbench workbench = PlatformUI.getWorkbench();
					IWorkbenchPage page = workbench.getActiveWorkbenchWindow().getActivePage();
					IViewPart view;
					if ((view = page.findView(SVUiPlugin.PLUGIN_ID + ".diagramView")) == null) {
						view = page.showView(SVUiPlugin.PLUGIN_ID + ".diagramView");
					}
					
					IDiagModelFactory factory = null ;
					
					if(itemBase.getType() == SVDBItemType.ClassDecl) {
						factory = new ClassDiagModelFactory(fEditor.getSVDBIndex(), (SVDBClassDecl)itemBase) ;
					} else if(itemBase.getType() == SVDBItemType.PackageDecl) {
						factory = new PackageClassDiagModelFactory(fEditor.getSVDBIndex(), (SVDBPackageDecl)itemBase) ;
					} else if (itemBase.getType() == SVDBItemType.ModuleDecl) {
						factory = new ModuleDiagModelFactory(fEditor.getSVDBIndex(), (SVDBModuleDecl)itemBase) ;
					}
						
					if(factory != null) {
					
						DiagModel model = factory.build() ;

						page.activate(view);
						
						((SVDiagramView)view).setViewState(IWorkbenchPage.STATE_MAXIMIZED) ;
	
						((SVDiagramView)view).setTarget(model, factory, fEditor.getSVDBIndex());
						
					}

				} catch (Exception e) {
					e.printStackTrace();
				}			
			}
			
			monitor.done();
		}
	};
	
}
