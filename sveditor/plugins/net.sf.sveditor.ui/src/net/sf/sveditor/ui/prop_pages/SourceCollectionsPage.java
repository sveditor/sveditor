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


package net.sf.sveditor.ui.prop_pages;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.project.SVDBSourceCollection;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.ui.SVUiPlugin;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.window.Window;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;


public class SourceCollectionsPage implements ISVProjectPropsPage,
	ITreeContentProvider, ILabelProvider {
	
	private TreeViewer						fSourceCollectionsTree;
	private SVProjectFileWrapper			fFileWrapper;
	private Button							fAddButton;
	private Button							fEditButton;
	private Button							fRemoveButton;
	private List<SVDBSourceCollection>		fSourceCollections;
	private IProject						fProject;
	
	public SourceCollectionsPage(IProject p) {
		fSourceCollections = new ArrayList<SVDBSourceCollection>();
		fProject = p;
	}

	public void init(SVProjectFileWrapper project_wrapper) {
		fFileWrapper = project_wrapper;
		fSourceCollections.clear();
		fSourceCollections.addAll(fFileWrapper.getSourceCollections());
	}

	/**
	 * @wbp.parser.entryPoint
	 */
	public Control createContents(Composite parent) {
		Composite frame = new Composite(parent, SWT.NONE);
		frame.setLayout(new GridLayout(2, false));
		

		fSourceCollectionsTree = new TreeViewer(frame, SWT.BORDER);
		fSourceCollectionsTree.getControl().setLayoutData(
				new GridData(SWT.FILL, SWT.FILL, true, true));
		fSourceCollectionsTree.addSelectionChangedListener(new ISelectionChangedListener() {
		
			public void selectionChanged(SelectionChangedEvent event) {
				updateSelection();
			}
		});
		fSourceCollectionsTree.setContentProvider(this);
		fSourceCollectionsTree.setLabelProvider(this);
		fSourceCollectionsTree.setInput(fSourceCollections);
		

		Composite button_bar = new Composite(frame, SWT.NONE);
		button_bar.setLayout(new GridLayout(1, true));

		fAddButton = new Button(button_bar, SWT.PUSH);
		fAddButton.setText("Add...");
		fAddButton.addSelectionListener(new SelectionListener() {

			public void widgetSelected(SelectionEvent e) {
				add();
			}
			
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		
		fEditButton = new Button(button_bar, SWT.PUSH);
		fEditButton.setText("Edit...");
		fEditButton.addSelectionListener(new SelectionListener(){
		
			public void widgetSelected(SelectionEvent e) {
				edit();
			}
		
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		
		fRemoveButton = new Button(button_bar, SWT.PUSH);
		fRemoveButton.setText("Remove");
		fRemoveButton.addSelectionListener(new SelectionListener(){
		
			public void widgetSelected(SelectionEvent e) {
				remove();
			}
		
			public void widgetDefaultSelected(SelectionEvent e) {}
		});
		
		updateSelection();

		return frame;
	}
	
	private void updateSelection() {
		IStructuredSelection sel = 
			(IStructuredSelection)fSourceCollectionsTree.getSelection();
		
		if (sel != null && sel.size() != 0) {
			if (sel.size() == 1 && sel.getFirstElement() instanceof SVDBSourceCollection) {
				fEditButton.setEnabled(true);
			} else {
				fEditButton.setEnabled(false);
			}
			fRemoveButton.setEnabled(true);
		} else {
			fRemoveButton.setEnabled(false);
		}
	}
	
	private void add() {
		AddSourceCollectionDialog dlg = new AddSourceCollectionDialog(fAddButton.getShell(), fProject);
		dlg.setIncludes(SVCorePlugin.getDefault().getDefaultSourceCollectionIncludes());
		dlg.setExcludes(SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes());
		
		if (dlg.open() == Window.OK) {
			// Add a new source collection
			SVDBSourceCollection sc = new SVDBSourceCollection(dlg.getBase(), dlg.getUseDefaultPattern());
			if (!dlg.getUseDefaultPattern()) {
				sc.getIncludes().addAll(
						SVDBSourceCollection.parsePatternList(dlg.getIncludes()));
				sc.getExcludes().addAll(
						SVDBSourceCollection.parsePatternList(dlg.getExcludes()));
			}
			
			fSourceCollections.add(sc);
			fSourceCollectionsTree.refresh();
		}
	}
	
	private void edit() {
		IStructuredSelection sel = 
			(IStructuredSelection)fSourceCollectionsTree.getSelection();
		
		if (sel != null && sel.size() == 1) {
			AddSourceCollectionDialog dlg = new AddSourceCollectionDialog(fEditButton.getShell(), fProject);
			SVDBSourceCollection sc = (SVDBSourceCollection)sel.getFirstElement();
			
			dlg.setBase(sc.getBaseLocation());
			dlg.setUseDefaultPattern(sc.getDefaultIncExcl());
			dlg.setIncludes(sc.getIncludesStr());
			dlg.setExcludes(sc.getExcludesStr());
			
			if (dlg.open() == Window.OK) {
				// Add a new source collection
				int sc_idx = fSourceCollections.indexOf(sc);
				sc = new SVDBSourceCollection(dlg.getBase(), dlg.getUseDefaultPattern());
				
				if (!dlg.getUseDefaultPattern()) {
					sc.getIncludes().addAll(
							SVDBSourceCollection.parsePatternList(dlg.getIncludes()));
					sc.getExcludes().addAll(
							SVDBSourceCollection.parsePatternList(dlg.getExcludes()));
				} else {
					
				}
				
				fSourceCollections.set(sc_idx, sc);
				fSourceCollectionsTree.refresh();
			}
		}
	}
	
	private void remove() {
		IStructuredSelection sel = 
			(IStructuredSelection)fSourceCollectionsTree.getSelection();
		
		if (sel != null && sel.size() > 0) {
			for (Object s_o : sel.toList()) {
				fSourceCollections.remove(s_o);
			}
		}
		
		fSourceCollectionsTree.refresh();
	}

	public Image getIcon() {
		return SVUiPlugin.getImage("/icons/eview16/source_collection.gif");
	}

	public String getName() {
		return "Source Collections";
	}

	public void perfomOk() {
		fFileWrapper.getSourceCollections().clear();
		fFileWrapper.getSourceCollections().addAll(fSourceCollections);
	}

	public Object[] getElements(Object inputElement) {
		return fSourceCollections.toArray();
	}

	public void dispose() {}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}

	public Image getImage(Object element) {
		return null;
	}

	public String getText(Object element) {
		if (element instanceof SVDBSourceCollection) {
			return ((SVDBSourceCollection)element).getBaseLocation();
		} else if (element instanceof IncExclWrapper) {
			return ((IncExclWrapper)element).fLabel;
		}
		return null;
	}

	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof SVDBSourceCollection) {
			SVDBSourceCollection sc = (SVDBSourceCollection)parentElement;
			IncExclWrapper inc = new IncExclWrapper();
			inc.fParent = sc;

			if (sc.getDefaultIncExcl()) {
				inc.fLabel = "Includes: (Default) " + sc.getIncludesStr();
			} else {
				inc.fLabel = "Includes: " + sc.getIncludesStr();
			}
			
			IncExclWrapper exc = new IncExclWrapper();
			exc.fParent = sc;

			if (sc.getDefaultIncExcl()) {
				exc.fLabel = "Excludes: (Default) " + sc.getExcludesStr();
			} else {
				exc.fLabel = "Excludes: " + sc.getExcludesStr();
			}

			return new Object[] {inc, exc}; 
		} else {
			return new Object[0];
		}
	}

	public Object getParent(Object element) {
		if (element instanceof IncExclWrapper) {
			return ((IncExclWrapper)element).fParent;
		}
		
		return null;
	}

	public boolean hasChildren(Object element) {
		return (element instanceof SVDBSourceCollection);
	}

	public void addListener(ILabelProviderListener listener) {}

	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	public void removeListener(ILabelProviderListener listener) {}

	private class IncExclWrapper {
		public String				fLabel;
		public SVDBSourceCollection	fParent;
	}
}
