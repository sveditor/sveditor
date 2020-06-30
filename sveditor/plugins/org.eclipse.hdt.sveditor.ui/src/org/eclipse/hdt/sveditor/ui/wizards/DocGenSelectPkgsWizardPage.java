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
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package org.eclipse.hdt.sveditor.ui.wizards;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.hdt.sveditor.ui.SVDBIconUtils;
import org.eclipse.hdt.sveditor.ui.SVUiPlugin;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindPackageMatcher;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.dialogs.FilteredTree;
import org.eclipse.ui.dialogs.PatternFilter;

public class DocGenSelectPkgsWizardPage extends WizardPage {
	
	private FilteredTree fLeftList ;
	private FilteredTree fRightList ;
	
	class MyListLabelProv extends LabelProvider{
		@Override
		public String getText(Object element) {
			@SuppressWarnings("unchecked")
			Tuple<SVDBDeclCacheItem, ISVDBIndex> item = (Tuple<SVDBDeclCacheItem, ISVDBIndex>) element ;
			return item.first().getName();
		}
	}
	
	public Boolean fSelectPackages ;
	
	private Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> fPkgMap ;

	private Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> fPackagesLeft ;
	private Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> fPackagesRight ;
	private Button fButtonAddSelected;
	private Button fButtonClearAll;
	private Button fButtonAddAll;
	private Button fButtonRemoveSelected;

	public Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> getPkgMap() {
		return fPkgMap ;
	}
	
	public Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> getSelectedPackages() {
		return fSelectPackages ? fPackagesRight : fPkgMap ;
	}

	protected DocGenSelectPkgsWizardPage() {
		super("Select Packages", "Select Packages", SVUiPlugin.getImageDescriptor("/icons/wizards/ndoc_wiz.png")) ;
		setDescription("Select the packages for which the documentation is to be generated for");
		fPackagesLeft = new HashMap<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>>() ;
		fPackagesRight = new HashMap<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>>() ;
		fPkgMap = new HashMap<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>>() ;
		fSelectPackages = new Boolean(false) ;
	}
	
	private void updatePackagesLeft() {
		fPackagesLeft.clear();
		if(fSelectPackages) {
			for(Tuple<SVDBDeclCacheItem,ISVDBIndex> tuple: fPkgMap.values()) {
				SVDBDeclCacheItem pkg = tuple.first() ;
				if(!fPackagesRight.containsKey(pkg)) {
					fPackagesLeft.put(pkg,tuple) ;
				}
			}
		}
		fLeftList.getViewer().setInput(fPackagesLeft) ;
	}

	public void createControl(Composite parent) {
		
		Composite container = new Composite(parent, SWT.NULL) ;
		final GridLayout gridLayout = new GridLayout() ;
		gridLayout.numColumns = 3 ;
		container.setLayout(gridLayout) ;
		setControl(container) ;
		
		createLeftTable(container) ;		
		createSelectionControls(container) ;
		createRightTable(container) ;		
		
		List<ISVDBIndex> projIndexList = SVCorePlugin.getDefault().getSVDBIndexRegistry().getAllProjectLists() ;
		for(ISVDBIndex svdbIndex: projIndexList) {
			List<SVDBDeclCacheItem> pkgs = svdbIndex.findGlobalScopeDecl(new NullProgressMonitor(),"pkgs",new SVDBFindPackageMatcher()) ;
			for(SVDBDeclCacheItem pkg: pkgs) {
				if(!fPkgMap.containsKey(pkg)) {
					fPkgMap.put(pkg, new Tuple<SVDBDeclCacheItem,ISVDBIndex>(pkg,svdbIndex)) ; 
				}
			}
		}		
		
		updatePackagesLeft() ;
		updateButtonEnables();
		
		fRightList.getViewer().setInput(fPackagesRight) ;
		
	}
	
	private void addAllOnLeft() {
		fPackagesRight.clear() ;
		for(SVDBDeclCacheItem item: fPackagesLeft.keySet()) {
			fPackagesRight.put(item, fPackagesLeft.get(item)) ;
		}
		fPackagesLeft .clear() ;
		fRightList.getViewer().setInput (fPackagesRight) ;
		fLeftList .getViewer().setInput (fPackagesLeft ) ;
	}

	private void createSelectionControls(Composite parent) {
		Composite container = new Composite(parent, SWT.NULL) ;
		
		container.setLayoutData(new GridData(GridData.FILL_VERTICAL)) ;
		container.setLayout(new RowLayout(SWT.VERTICAL)) ;
		
		Group group = new Group(container, SWT.NONE) ;
		group.setLayout(new RowLayout(SWT.VERTICAL));
		
		/**
		 * Button to Add all packages to the right hand side
		 */
		fButtonAddAll = new Button(group,SWT.PUSH) ;
		fButtonAddAll.setText("&Select All") ;
		fButtonAddAll.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				addAllOnLeft() ;
				updatePageComplete() ;
			}
		}) ;
		
		/**
		 * Button to Clear all from the right to the left
		 */
		fButtonClearAll = new Button(group,SWT.PUSH) ;
		fButtonClearAll.setText("&Clear All") ;
		fButtonClearAll.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fPackagesRight.clear() ;
				updatePackagesLeft() ;
				fLeftList .getViewer().setInput(fPackagesLeft ) ;
				fRightList.getViewer().setInput(fPackagesRight) ;
				updatePageComplete() ;
			}
		}) ;

		/**
		 * Button to Button to add currently selected items
		 */
		fButtonAddSelected = new Button(group,SWT.PUSH) ;
		fButtonAddSelected.setText("&Add Selected") ;
		fButtonAddSelected.addSelectionListener(new SelectionAdapter() {
			@SuppressWarnings("unchecked")
			@Override
			public void widgetSelected(SelectionEvent e) {
				Tuple<SVDBDeclCacheItem, ISVDBIndex> item ; 
				TreeSelection selection = (TreeSelection) fLeftList.getViewer().getSelection();
				if(selection != null) {
					for (Iterator<?> iterator = selection.iterator(); iterator.hasNext();) {
						item = (Tuple<SVDBDeclCacheItem,ISVDBIndex>) iterator.next() ;
						fPackagesLeft.remove(item.first()) ;
						fPackagesRight.put(item.first(),item) ;
					}
				}
				fLeftList .getViewer().setInput(fPackagesLeft) ;
				fRightList.getViewer().setInput(fPackagesRight) ;
				updatePageComplete() ;
			}
		}) ;

		/**
		 * Button to Button to remove selected items
		 */
		fButtonRemoveSelected = new Button(group,SWT.PUSH) ;
		fButtonRemoveSelected.setText("&Remove Selected") ;
		fButtonRemoveSelected.addSelectionListener(new SelectionAdapter() {
			@SuppressWarnings("unchecked")
			@Override
			public void widgetSelected(SelectionEvent e) {
				Tuple<SVDBDeclCacheItem, ISVDBIndex> item ; // new SVDBDeclCacheItem();
				TreeSelection selection = (TreeSelection) fRightList.getViewer().getSelection();
				if ((selection != null) && (selection.getFirstElement() instanceof Tuple<?,?>))  {
                    item = (Tuple<SVDBDeclCacheItem,ISVDBIndex>) selection.getFirstElement() ;
                    if(fPkgMap.containsKey(item.first())) {
                    	fPackagesRight.remove(item.first()) ;
                    	if(fSelectPackages) {
							fPackagesLeft.put(item.first(),item) ;
                        }
                    }
				}
				fLeftList .getViewer().setInput(fPackagesLeft) ;
				fRightList.getViewer().setInput(fPackagesRight) ;
				updatePageComplete() ;
			}
		}) ;
		
		/**
		 * Goup to contain misc options
		 */

		group = new Group(container, SWT.NONE) ;
		group.setLayout(new RowLayout(SWT.VERTICAL));
		
		/**
		 * Check Button to enable package selection
		 */
		final Button buttonShowPackages = new Button(group, SWT.CHECK) ;
		buttonShowPackages.setText("Select &Packages") ;
		buttonShowPackages.setSelection(fSelectPackages);
		buttonShowPackages.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fSelectPackages = buttonShowPackages.getSelection() ;
				updatePackagesLeft();
				fLeftList .getViewer().setInput(fPackagesLeft) ;
				updateButtonEnables() ;
				updatePageComplete() ;
			}
		}) ;
		


	}

	protected void updateButtonEnables() {
		
		fButtonAddAll.setEnabled(fSelectPackages);
		fButtonClearAll.setEnabled(fSelectPackages);
		fButtonAddSelected.setEnabled(fSelectPackages);
		fButtonRemoveSelected.setEnabled(fSelectPackages);
		
	}

	private void createLeftTable(Composite parent) {
		
		fLeftList = new FilteredTree(parent, SWT.H_SCROLL|SWT.V_SCROLL, new PatternFilter(),true) ;
		
		fLeftList.setLayoutData(new GridData(GridData.FILL_BOTH)) ;
		fLeftList.getViewer().setLabelProvider( new MyListLabelProv()) ;
			
		
		TreeViewer viewer = fLeftList.getViewer() ;
				
		viewer.setContentProvider(new ITreeContentProvider() {
			Object fInput ;
			public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
				fInput = newInput ;
			}
			public void dispose() {}
			public boolean hasChildren(Object element) { return false ; }
			public Object getParent(Object element) { return null; }
			public Object[] getElements(Object inputElement) {
				if(fInput instanceof HashMap<?,?>) {
					return ((HashMap<?,?>)fInput).values().toArray() ;
				} else {
					return new Object[0] ;
				}
			}
			public Object[] getChildren(Object parentElement) {
				return null;
			}
		}) ;
		
		viewer.setLabelProvider(new LabelProvider() {
			@SuppressWarnings("unchecked")
			@Override
			public String getText(Object element) {
				if(element instanceof Tuple<?,?>) {
					return ((Tuple<SVDBDeclCacheItem,ISVDBIndex>)element).first().getName() ; 
				} else {
					return "<unexpected-item-type>" ;
				}
			}
			@SuppressWarnings("unchecked")
			@Override
			public Image getImage(Object element) {
				if(element instanceof Tuple<?,?>) {
					return SVDBIconUtils.getIcon(((Tuple<SVDBDeclCacheItem,ISVDBIndex>)element).first().getType()) ; 
				}
				return super.getImage(element) ;
			}
		}) ;		
		
	}

	private void createRightTable(Composite parent) {
	
		fRightList = new FilteredTree(parent, SWT.H_SCROLL|SWT.V_SCROLL, new PatternFilter(),true) ;
		
		fRightList.setLayoutData(new GridData(GridData.FILL_BOTH)) ;
		
		TreeViewer viewer = fRightList.getViewer() ;
				
		viewer.setContentProvider(new ITreeContentProvider() {
			Object fInput ;
			public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
				fInput = newInput ;
			}
			public void dispose() {}
			public boolean hasChildren(Object element) { return false ; }
			public Object getParent(Object element) { return null; }
			public Object[] getElements(Object inputElement) {
				if(fInput instanceof HashMap<?,?>) {
					return ((HashMap<?,?>)fInput).values().toArray() ;
				} else {
					return new Object[0] ;
				}
			}
			public Object[] getChildren(Object parentElement) {
				return null;
			}
		}) ;
		
		viewer.setLabelProvider(new LabelProvider() {
			@SuppressWarnings("unchecked")
			@Override
			public String getText(Object element) {
				if(element instanceof Tuple<?,?>) {
					return ((Tuple<SVDBDeclCacheItem,ISVDBIndex>)element).first().getName() ; 
				} else {
					return "<unexpected-item-type>" ;
				}
			}
			@SuppressWarnings("unchecked")
			@Override
			public Image getImage(Object element) {
				if(element instanceof Tuple<?,?>) {
					return SVDBIconUtils.getIcon(((Tuple<SVDBDeclCacheItem,ISVDBIndex>)element).first().getType()) ; 
				}
				return super.getImage(element) ;
			}
		}) ;		
	}

	public boolean hasSelection() {
		return fPackagesRight.size() != 0 ;
	}
	
	protected void updatePageComplete() {
		if(fSelectPackages) {
			setPageComplete(hasSelection()) ;
		} else {
			setPageComplete(true) ;
		}
	}

}
