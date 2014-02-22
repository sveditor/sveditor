/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.ui.wizards;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.search.SVDBFindPackageMatcher;
import net.sf.sveditor.ui.SVDBIconUtils;

import org.eclipse.core.runtime.NullProgressMonitor;
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
import org.eclipse.swt.widgets.Label;
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
	
	private Boolean fShowModules ;
	private Boolean fShowPackages ;
	private Boolean fShowPrograms ;
	
	private Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> fPkgMap ;
	private Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> fModuleMap ;
	private Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> fProgramMap ;

	private Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> fPackagesLeft ;
	private Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> fPackagesRight ;

	public Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> getPkgMap() {
		return fPkgMap ;
	}
	public Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> getModuleMap() {
		return fModuleMap ;
	}
	public Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> getProgramMap() {
		return fProgramMap ;
	}
	
	public Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> getSelectedPackages() {
		return fPackagesRight;
	}

	protected DocGenSelectPkgsWizardPage() {
		super("Select Packages") ;
		fPackagesLeft = new HashMap<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>>() ;
		fPackagesRight = new HashMap<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>>() ;
		fPkgMap = new HashMap<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>>() ;
		fShowModules = new Boolean(false) ;
		fShowPackages = new Boolean(true) ;
		fShowPrograms = new Boolean(false) ;
	}
	
	private void updatePackagesLeft() {
		fPackagesLeft.clear();
		if(fShowPackages) {
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
		
		createLabel(container);
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
		Button button ;
		
		container.setLayoutData(new GridData(GridData.FILL_VERTICAL)) ;
		container.setLayout(new RowLayout(SWT.VERTICAL)) ;
		
		Group group = new Group(container, SWT.NONE) ;
		group.setLayout(new RowLayout(SWT.VERTICAL));
		
		/**
		 * Button to Add all packages to the right hand side
		 */
		button = new Button(group,SWT.PUSH) ;
		button.setText("&Select All") ;
		button.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				addAllOnLeft() ;
				updatePageComplete() ;
			}
		}) ;
		
		/**
		 * Button to Clear all from the right to the left
		 */
		button = new Button(group,SWT.PUSH) ;
		button.setText("&Clear All") ;
		button.addSelectionListener(new SelectionAdapter() {
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
		button = new Button(group,SWT.PUSH) ;
		button.setText("&Add Selected") ;
		button.addSelectionListener(new SelectionAdapter() {
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
		button = new Button(group,SWT.PUSH) ;
		button.setText("&Remove Selected") ;
		button.addSelectionListener(new SelectionAdapter() {
			@SuppressWarnings("unchecked")
			@Override
			public void widgetSelected(SelectionEvent e) {
				Tuple<SVDBDeclCacheItem, ISVDBIndex> item ; // new SVDBDeclCacheItem();
				TreeSelection selection = (TreeSelection) fRightList.getViewer().getSelection();
				if ((selection != null) && (selection.getFirstElement() instanceof Tuple<?,?>))  {
                    item = (Tuple<SVDBDeclCacheItem,ISVDBIndex>) selection.getFirstElement() ;
                    if(fPkgMap.containsKey(item.first())) {
                    	fPackagesRight.remove(item.first()) ;
                    	if(fShowPackages) {
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
		 * Check Button to show Packages
		 */
		final Button buttonShowPackages = new Button(group, SWT.CHECK) ;
		buttonShowPackages.setText("Show &Packages") ;
		buttonShowPackages.setSelection(fShowPackages);
		buttonShowPackages.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fShowPackages = buttonShowPackages.getSelection() ;
				updatePackagesLeft();
				fLeftList .getViewer().setInput(fPackagesLeft) ;
				updatePageComplete() ;
			}
		}) ;
		

		/**
		 * Check Button to show modules
		 */
		final Button buttonShowModules = new Button(group, SWT.CHECK) ;
		buttonShowModules.setText("Show &Modules") ;
		buttonShowModules.setSelection(fShowModules);
		buttonShowModules.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fShowModules = buttonShowModules.getSelection() ;
				updatePackagesLeft();
				fLeftList .getViewer().setInput(fPackagesLeft) ;
				updatePageComplete() ;
			}
		}) ;
		

		/**
		 * Check Button to show programs
		 */
		final Button buttonShowProgs = new Button(group, SWT.CHECK) ;
		buttonShowProgs.setText("Show &Programs") ;
		buttonShowProgs.setSelection(fShowPrograms);
		buttonShowProgs.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fShowPrograms = buttonShowProgs.getSelection() ;
				updatePackagesLeft();
				fLeftList .getViewer().setInput(fPackagesLeft) ;
				updatePageComplete() ;
			}
		}) ;
		

	}

	private void createLabel(Composite container) {
		final Label label = new Label(container, SWT.NONE) ; 
		final GridData gridData = new GridData() ;
		gridData.horizontalSpan = 3 ;
		label.setLayoutData(gridData) ;
		label.setText( "Select the packages for which the documentation is to be generated for" ) ;
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
		setPageComplete(hasSelection()) ;
	}

}
