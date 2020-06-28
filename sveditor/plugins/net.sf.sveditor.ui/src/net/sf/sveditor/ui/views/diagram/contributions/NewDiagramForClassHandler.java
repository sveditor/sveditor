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
 *     Armond Paiva - initial contributor
 ****************************************************************************/

package net.sf.sveditor.ui.views.diagram.contributions;

import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.diagrams.ClassDiagModelFactory;
import net.sf.sveditor.core.diagrams.DiagModel;
import net.sf.sveditor.core.diagrams.IDiagModelFactory;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.views.diagram.SVDiagramView;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

public class NewDiagramForClassHandler extends AbstractHandler implements IHandler {
	
	private ISVDBIndex fSVDBIndex ;
	
	public NewDiagramForClassHandler() { }
	
	public void setSVDBIndex(ISVDBIndex index) {
		fSVDBIndex = index ;
	}
	
	public Object execute(ExecutionEvent event) throws ExecutionException {
		if(event.getApplicationContext() instanceof SVDBClassDecl && fSVDBIndex != null) {
			SVDBClassDecl classDecl = (SVDBClassDecl)event.getApplicationContext() ;
			IDiagModelFactory factory = new ClassDiagModelFactory(fSVDBIndex, classDecl) ;
			IWorkbench workbench = PlatformUI.getWorkbench();
			IWorkbenchPage page = workbench.getActiveWorkbenchWindow().getActivePage();
			IViewPart view;
			try {
//				String viewName = classDecl.getName() ;
				if ((view = page.findView(SVUiPlugin.PLUGIN_ID + ".diagramView")) == null) {
					view = page.showView(SVUiPlugin.PLUGIN_ID + ".diagramView") ;
				}
				DiagModel model = factory.build() ;
				if(model == null) { return null ; }
//				view = page.showView(SVUiPlugin.PLUGIN_ID + ".diagramView", viewName, IWorkbenchPage.VIEW_VISIBLE) ;
//				view = page.showView(SVUiPlugin.PLUGIN_ID + ".diagramView");
				page.activate(view) ;
				((SVDiagramView)view).setViewState(IWorkbenchPage.STATE_MAXIMIZED) ;
				((SVDiagramView)view).setTarget(model, factory, fSVDBIndex);
			} catch (PartInitException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		return null ;
	}

}
