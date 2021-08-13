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

package org.sveditor.ui.views.diagram.contributions;

import java.util.Collections;

import org.sveditor.ui.SVDBIconUtils;
import org.sveditor.ui.views.diagram.SVDiagramView;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.sveditor.core.db.SVDBClassDecl;
import org.sveditor.core.diagrams.DiagNode;
import org.eclipse.jface.action.ContributionItem;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.MenuItem;

public class NewDiagramForClassContributionItem extends ContributionItem {
	
	protected final SVDiagramView fDiagramView ;
	protected final IHandler fHandler ;
	
	boolean fEnabled = false ;
	
	private MenuItem fMenuItem ;
	private SVDBClassDecl fClassDecl ;
	
	public NewDiagramForClassContributionItem(SVDiagramView diagramView, IHandler handler) {
		fDiagramView = diagramView ; 
		fHandler = handler ;
		fDiagramView.getGraphViewer().addSelectionChangedListener(
				new ISelectionChangedListener() {
					public void selectionChanged(SelectionChangedEvent event) {
						ISelection selection = event.getSelection() ;
						fEnabled = false ; fClassDecl = null ;
						if(!selection.isEmpty() && selection instanceof IStructuredSelection) {
							IStructuredSelection structuredSel = (IStructuredSelection)selection ;
							if(structuredSel.size() == 1) {  
								if(structuredSel.getFirstElement() instanceof DiagNode) { 
									DiagNode node = (DiagNode)structuredSel.getFirstElement() ;
									if(node.getSVDBItem() instanceof SVDBClassDecl) {
										fEnabled = true ;
										fClassDecl = (SVDBClassDecl)node.getSVDBItem() ;
									} 
								}
							}
						}
						updateEnablement() ;
					}
				} ) ;
	}
	
	@Override
	public boolean isDynamic() {
		return true ;
	}

	protected void updateEnablement() {
		if(fMenuItem!= null) {
			fMenuItem.setEnabled(fEnabled) ;
		}
	}

	@Override
	public void fill(Menu menu, int index) {
		if(fClassDecl == null) { return ; } 
		fMenuItem = new MenuItem(menu, SWT.NONE, index) ;
		fMenuItem.setText("Create new Class Diagram for \""
			+ fClassDecl.getName()
			+ "\"") ;
		fMenuItem.setImage(SVDBIconUtils.getIcon(fClassDecl)) ; // TODO: find a good diagram icon
		fMenuItem.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				run() ;
			}
		}) ;
		updateEnablement() ;
	}

	protected void run() {
		ExecutionEvent event = new ExecutionEvent(null, Collections.EMPTY_MAP, null, fClassDecl) ;
		try {
			fHandler.execute(event) ;
		}
		catch (ExecutionException e ) { 
			// TODO: handle exception
		}
	}
	

}
