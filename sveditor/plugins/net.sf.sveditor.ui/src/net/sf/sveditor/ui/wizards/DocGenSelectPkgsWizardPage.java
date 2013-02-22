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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.dialogs.FilteredTree;
import org.eclipse.ui.dialogs.PatternFilter;

public class DocGenSelectPkgsWizardPage extends WizardPage {
	
	private FilteredTree fLeftList ;
	private FilteredTree fRightList ;
	
	private Set<SVDBDeclCacheItem> fPackagesLeft ; 
	private Set<SVDBDeclCacheItem> fPackagesRight ; 
	
	Map<String,Tuple<SVDBDeclCacheItem, ISVDBIndex>> fPkgMap ;

	
	public Map<String,Tuple<SVDBDeclCacheItem, ISVDBIndex>> getPkgMap() {
		return fPkgMap ;
	}
	
	public Set<SVDBDeclCacheItem> getSelectedPackages() {
		return fPackagesRight;
	}

	public void setfSelectedPackages(Set<SVDBDeclCacheItem> fSelectedPackages) {
		this.fPackagesRight = fSelectedPackages;
	}

	protected DocGenSelectPkgsWizardPage() {
		super("Select Packages") ;
		fPackagesLeft = new HashSet<SVDBDeclCacheItem>() ;
		fPackagesRight = new HashSet<SVDBDeclCacheItem>() ;
		fPkgMap = new HashMap<String,Tuple<SVDBDeclCacheItem, ISVDBIndex>>() ;
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
				if(!fPkgMap.containsKey(pkg.getName())) { fPkgMap.put(pkg.getName(), new Tuple<SVDBDeclCacheItem,ISVDBIndex>(pkg,svdbIndex)) ; }
			}
		}		
		
		for(Tuple<SVDBDeclCacheItem,ISVDBIndex> tuple: fPkgMap.values()) {
			fPackagesLeft.add(tuple.first()) ;
		}
		
		fLeftList.getViewer().setInput(fPackagesLeft) ;
		fRightList.getViewer().setInput(fPackagesRight) ;
		
	}

	private void createSelectionControls(Composite parent) {
		Composite container = new Composite(parent, SWT.NULL) ;
		Button button ;
		
		container.setLayoutData(new GridData(GridData.FILL_VERTICAL)) ;
		container.setLayout(new RowLayout(SWT.VERTICAL)) ;
		
		/**
		 * Add all packages to the right hand side
		 */
		button = new Button(container,SWT.PUSH) ;
		button.setText("&Select All") ;
		button.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fPackagesLeft .clear() ;
				fPackagesRight.clear() ;
				for(Tuple<SVDBDeclCacheItem,ISVDBIndex> tuple: fPkgMap.values()) {
					fPackagesRight.add(tuple.first()) ;
				}
				fRightList.getViewer().setInput (fPackagesRight) ;
				fLeftList .getViewer().setInput (fPackagesLeft ) ;
				updatePageComplete() ;
			}
		}) ;
		
		/**
		 * Clear all from the right to the left
		 */
		button = new Button(container,SWT.PUSH) ;
		button.setText("&Clear All") ;
		button.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				for(Tuple<SVDBDeclCacheItem,ISVDBIndex> tuple: fPkgMap.values()) {
					fPackagesLeft.add(tuple.first()) ;
				}
				fPackagesRight.clear() ;
				fLeftList .getViewer().setInput(fPackagesLeft ) ;
				fRightList.getViewer().setInput(fPackagesRight) ;
				updatePageComplete() ;
			}
		}) ;

		/**
		 * Button to add currently selected items
		 */
		button = new Button(container,SWT.PUSH) ;
		button.setText("&Add Selected") ;
		button.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				SVDBDeclCacheItem svdbci = new SVDBDeclCacheItem();
				TreeSelection selection = (TreeSelection) fLeftList.getViewer().getSelection();
				if ((selection != null) && (selection.getFirstElement() instanceof SVDBDeclCacheItem))  {
					svdbci = (SVDBDeclCacheItem) selection.getFirstElement();
				}
				
				for(Tuple<SVDBDeclCacheItem,ISVDBIndex> tuple: fPkgMap.values()) {
					if (tuple.first().equals(svdbci))  {
						fPackagesLeft .remove(tuple.first()) ;
						fPackagesRight.add   (tuple.first()) ;
					}
				}
				fLeftList .getViewer().setInput(fPackagesLeft) ;
				fRightList.getViewer().setInput(fPackagesRight) ;
				updatePageComplete() ;
			}
		}) ;

		/**
		 * Button to remove selected items
		 */
		button = new Button(container,SWT.PUSH) ;
		button.setText("&Remove Selected") ;
		button.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				SVDBDeclCacheItem svdbci = new SVDBDeclCacheItem();
				TreeSelection selection = (TreeSelection) fRightList.getViewer().getSelection();
				if ((selection != null) && (selection.getFirstElement() instanceof SVDBDeclCacheItem))  {
					svdbci = (SVDBDeclCacheItem) selection.getFirstElement();
				}
				
				for(Tuple<SVDBDeclCacheItem,ISVDBIndex> tuple: fPkgMap.values()) {
					if (tuple.first().equals(svdbci))  {
						fPackagesLeft .add   (tuple.first()) ;
						fPackagesRight.remove(tuple.first()) ;
					}
				}
				fLeftList .getViewer().setInput(fPackagesLeft) ;
				fRightList.getViewer().setInput(fPackagesRight) ;
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
				if(fInput instanceof Collection<?>) {
					return ((Collection<?>)fInput).toArray() ;
				} else {
					return new Object[0] ;
				}
			}
			public Object[] getChildren(Object parentElement) {
				return null;
			}
		}) ;
		
		
		viewer.setLabelProvider(new LabelProvider() {
			@Override
			public String getText(Object element) {
				if(element instanceof SVDBDeclCacheItem) {
					return ((SVDBDeclCacheItem)element).getName() ;
				} else {
					return "<unexpected-item-type>" ;
				}
			}
			@Override
			public Image getImage(Object element) {
				if(element instanceof SVDBDeclCacheItem) {
					return SVDBIconUtils.getIcon(((SVDBDeclCacheItem)element).getType()) ;
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
				if(fInput instanceof Collection<?>) {
					return ((Collection<?>)fInput).toArray() ;
				} else {
					return new Object[0] ;
				}
			}
			public Object[] getChildren(Object parentElement) {
				return null;
			}
		}) ;
		
		viewer.setLabelProvider(new LabelProvider() {
			@Override
			public String getText(Object element) {
				if(element instanceof SVDBDeclCacheItem) {
					return ((SVDBDeclCacheItem)element).getName() ;
				} else {
					return "<unexpected-item-type>" ;
				}
			}
			@Override
			public Image getImage(Object element) {
				if(element instanceof SVDBDeclCacheItem) {
					return SVDBIconUtils.getIcon(((SVDBDeclCacheItem)element).getType()) ;
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
