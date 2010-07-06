/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBChangeListener;
import net.sf.sveditor.ui.svcp.SVDBDefaultContentFilter;
import net.sf.sveditor.ui.svcp.SVTreeContentProvider;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.part.IShowInTarget;
import org.eclipse.ui.part.ShowInContext;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

public class SVOutlinePage extends ContentOutlinePage 
	implements IShowInTarget, IAdaptable, 
			Runnable, ISVDBChangeListener {
	private SVTreeContentProvider		fContentProvider;
	private SVEditor					fEditor;
	private boolean						fIgnoreSelection = false;
	private SVDBItem					fLastSelection;
	
	public SVOutlinePage(SVEditor editor) {
		fEditor = editor;
		fContentProvider = new SVTreeContentProvider();
	}
	
	public void createControl(Composite parent) {
		super.createControl(parent);
		
		fContentProvider = new SVTreeContentProvider();
		
		getTreeViewer().setContentProvider(fContentProvider);
		getTreeViewer().addFilter(new SVDBDefaultContentFilter());
		getTreeViewer().setLabelProvider(new SVTreeLabelProvider());
		
		getTreeViewer().setInput(fEditor.getSVDBFile());
		
		getTreeViewer().getControl().getDisplay().asyncExec(this);
		
		getTreeViewer().addSelectionChangedListener(fSelectionListener);
		getTreeViewer().setAutoExpandLevel(TreeViewer.ALL_LEVELS);
	}

	
	public void SVDBFileChanged(SVDBFile file, List<SVDBItem> adds,
			List<SVDBItem> removes, List<SVDBItem> changes) {
		if (file.getFilePath().equals(fEditor.getFilePath())) {
			if (getTreeViewer() != null && !getTreeViewer().getControl().isDisposed()) {
				Display.getDefault().asyncExec(this);
				// Display.getDefault().timerExec(1000, this);
				// getTreeViewer().getControl().getDisplay().
			}
		}
	}
	
	public void refresh() {
		if (getTreeViewer() != null && !getTreeViewer().getControl().isDisposed()) {
			Display.getDefault().asyncExec(this);
		}
	}

	public void run() {
		if (getTreeViewer() != null && !getTreeViewer().getControl().isDisposed()) {
			getTreeViewer().refresh();
		}
	}

	public void dispose() {
		if (getTreeViewer() != null) {
			getTreeViewer().removeSelectionChangedListener(fSelectionListener);
		}
	}

	@SuppressWarnings("unchecked")
	public Object getAdapter(Class adapter) {
		if (IShowInTarget.class.equals(adapter)) {
			return this;
		}
		return null;
	}

	
	public boolean show(ShowInContext context) {
		// TODO Auto-generated method stub
		return true;
	}
	
	private ISelectionChangedListener fSelectionListener = 
		new ISelectionChangedListener() {

			
			public void selectionChanged(SelectionChangedEvent event) {
				if (fIgnoreSelection) {
					return;
				}
				
				removeSelectionChangedListener(this);
				
				if (event.getSelection() instanceof StructuredSelection) {
					StructuredSelection sel = (StructuredSelection)event.getSelection();
					if (sel.getFirstElement() instanceof SVDBItem) {
						SVDBItem it = (SVDBItem)sel.getFirstElement();
						
						if (fLastSelection == null || fLastSelection != it) {
							fEditor.setSelection(it, false);
							fLastSelection = it;
						}
					}
				}
				
				addSelectionChangedListener(this);
			}
	};
	
}
