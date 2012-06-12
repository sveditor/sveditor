/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial contributor
 ****************************************************************************/

package net.sf.sveditor.ui.views.diagram;

import net.sf.sveditor.ui.SVDBIconUtils;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.viewers.IBaseLabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.ImageLoader;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.zest.core.viewers.AbstractZoomableViewer;
import org.eclipse.zest.core.viewers.GraphViewer;
import org.eclipse.zest.core.viewers.IZoomableWorkbenchPart;
import org.eclipse.zest.layouts.LayoutStyles;
import org.eclipse.zest.layouts.algorithms.GridLayoutAlgorithm;
import org.eclipse.zest.layouts.algorithms.HorizontalLayoutAlgorithm;
import org.eclipse.zest.layouts.algorithms.RadialLayoutAlgorithm;
import org.eclipse.zest.layouts.algorithms.TreeLayoutAlgorithm;


public class SVDiagramView extends ViewPart implements SelectionListener, IZoomableWorkbenchPart {
	
	private GraphViewer fGraphViewer ;
	private DiagModel fModel ;
	private IDiagModelFactory fModelFactory ;
	private CTabItem fConfigTab ;
	private CTabFolder fTabFolder ;
	private IDiagLabelProviderConfig fDiagLabelProvider ;
	
	@Override
	public void createPartControl(Composite parent) {
		
		GridLayout gl = new GridLayout() ;
		GridData gd = null ;
		Group group = null ;
		
		gl.numColumns = 2 ;
		parent.setLayout(gl) ;
		
		fGraphViewer = new GraphViewer(parent, SWT.BORDER) ;
		fDiagLabelProvider = new DiagLabelProvider() ;
		fGraphViewer.setContentProvider(new NodeContentProvider()) ;
		fGraphViewer.setLabelProvider((IBaseLabelProvider)fDiagLabelProvider) ;
		fGraphViewer.setInput(fModel == null ? null : fModel.getNodes()) ;
		
		gd = new GridData() ; 
		gd.grabExcessVerticalSpace = true ;
		gd.grabExcessHorizontalSpace = true ;
		gd.horizontalAlignment = GridData.FILL ;
		gd.verticalAlignment = GridData.FILL ;
		fGraphViewer.getControl().setLayoutData(gd) ;
		
		fTabFolder = new CTabFolder(parent, SWT.NONE) ;
		fTabFolder.setSimple(false) ;
		
		gd = new GridData() ;
		gd.grabExcessVerticalSpace = true ;
		gd.verticalAlignment = GridData.FILL ;
		gd.horizontalAlignment = GridData.FILL ;
		fTabFolder.setLayoutData(gd) ;
		
		fConfigTab = new CTabItem(fTabFolder, SWT.NONE); 
		fConfigTab.setText("Options") ;
		fConfigTab.setImage(SVDBIconUtils.getIcon(SVDBIconUtils.CONFIG_OBJ)) ;
		
		fConfigTab.setControl(new Composite(fTabFolder, SWT.NONE)) ; 
		((Composite)fConfigTab.getControl()).setLayout(new GridLayout()) ;
		
		group = new Group((Composite)fConfigTab.getControl(), SWT.NONE) ;
		group.setLayoutData(new GridData(GridData.FILL_HORIZONTAL)) ;
		group.setLayout(new RowLayout(SWT.VERTICAL)) ;
		group.setText("Layout") ;
		Button layoutRadios[] = new Button[4] ;
		layoutRadios[0] = new Button(group, SWT.RADIO) ;
		layoutRadios[0].setText("Radial") ;
		layoutRadios[0].addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fGraphViewer.setLayoutAlgorithm(new RadialLayoutAlgorithm(LayoutStyles.NO_LAYOUT_NODE_RESIZING)) ;
				fGraphViewer.applyLayout() ;
			}
		});
		layoutRadios[1] = new Button(group, SWT.RADIO) ;
		layoutRadios[1].setText("Grid") ;
		layoutRadios[1].setSelection(true) ;  // Default
		layoutRadios[1].addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fGraphViewer.setLayoutAlgorithm(new GridLayoutAlgorithm(LayoutStyles.NO_LAYOUT_NODE_RESIZING)) ;
				fGraphViewer.applyLayout() ;
			}
		});
		layoutRadios[2] = new Button(group, SWT.RADIO) ;
		layoutRadios[2].setText("Tree") ;
		layoutRadios[2].addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fGraphViewer.setLayoutAlgorithm(new TreeLayoutAlgorithm(LayoutStyles.NO_LAYOUT_NODE_RESIZING)) ;
				fGraphViewer.applyLayout() ;
			}
		});
		layoutRadios[3] = new Button(group, SWT.RADIO) ;
		layoutRadios[3].setText("Horizontal Tree") ;
		layoutRadios[3].addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fGraphViewer.setLayoutAlgorithm(new HorizontalLayoutAlgorithm(LayoutStyles.NO_LAYOUT_NODE_RESIZING)) ;
				fGraphViewer.applyLayout() ;
			}
		});
		
		
		//
		Button button = null ;
		
		group = new Group((Composite)fConfigTab.getControl(), SWT.NONE) ;
		group.setLayoutData(new GridData(GridData.FILL_HORIZONTAL)) ;
		group.setLayout(new RowLayout(SWT.VERTICAL)) ;
		group.setText("Class Details") ;
		button = new Button(group, SWT.CHECK) ;
		button.setText("Show tasks/function") ;
		button.setSelection(true) ;  // TODO: will want to configure this based upon scope
		fDiagLabelProvider.setIncludePrivateTasksFunctions(true) ; // TODO: 
		button.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fDiagLabelProvider.setIncludePublicTasksFunctions(((Button)(e.widget)).getSelection()) ;
				fDiagLabelProvider.setIncludePrivateTasksFunctions(((Button)(e.widget)).getSelection()) ;
				updateInputNoLayout() ;
			}
		}) ;
		button = new Button(group, SWT.CHECK) ;
		button.setText("Show fields") ;
		button.setSelection(true) ;  // TODO: will want to configure this based upon scope
		fDiagLabelProvider.setIncludePrivateClassFields(true) ; // TODO: 
		button.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fDiagLabelProvider.setIncludePublicClassFields(((Button)(e.widget)).getSelection()) ;
				fDiagLabelProvider.setIncludePrivateClassFields(((Button)(e.widget)).getSelection()) ;
				updateInputNoLayout() ;
			}
		}) ;
		button = new Button(group, SWT.CHECK) ;
		button.setText("Show field types") ;
		button.setSelection(false) ;
		fDiagLabelProvider.setShowFieldTypes(false) ;
		button.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fDiagLabelProvider.setShowFieldTypes(((Button)(e.widget)).getSelection()) ;
				updateInputNoLayout() ;
			}
		}) ;
		
		//
		//
		//
		
		IToolBarManager tbm = getViewSite().getActionBars().getToolBarManager() ;
		
		final Shell shell = parent.getShell() ;
		
		tbm.add( new Action("Export Image", Action.AS_PUSH_BUTTON) {
			{ setImageDescriptor(PlatformUI.getWorkbench().getSharedImages()
					.getImageDescriptor(ISharedImages.IMG_ETOOL_SAVEAS_EDIT)) ; }
			public void run() {
				FileDialog fileDialog = new FileDialog(shell, SWT.SAVE) ;
				fileDialog.setText("Select File");
				fileDialog.setFilterExtensions(new String[] { "*.png" });
				fileDialog.setFilterNames(new String[] { "PNG files (*.png)" });
				String selected = fileDialog.open() ;				
				if(selected != null) {
					GC gc = new GC(fGraphViewer.getControl());
					Rectangle bounds = fGraphViewer.getControl().getBounds() ;
					Image image = new Image(fGraphViewer.getControl().getDisplay(), bounds) ;
					try {
					    gc.copyArea(image, 0, 0);
					    ImageLoader imageLoader = new ImageLoader();
					    imageLoader.data = new ImageData[] { image.getImageData() } ;
					    imageLoader.save(selected, SWT.IMAGE_PNG) ;
					} finally {
					    image.dispose() ;
					    gc.dispose() ;
					}					
				}
			} }) ;
		
		//
		//
		//
		
		fGraphViewer.setLayoutAlgorithm(new GridLayoutAlgorithm(LayoutStyles.NO_LAYOUT_NODE_RESIZING)) ;
		fGraphViewer.applyLayout() ;
		
		fillToolbar() ;
		
		fTabFolder.setSelection(fConfigTab) ;
		
	}
	
	private void updateInputNoLayout() {
		fGraphViewer.setLayoutAlgorithm(new LeaveEmBeLayoutAlgoritm(SWT.NONE)) ;
		fGraphViewer.setInput(fModel.getNodes()) ;
	}
	
//	private void rebuildModel() {
//		// TODO: this might get slooooowwww for big diags
//		fModel = fModelFactory.build();
//		fGraphViewer.setInput(fModel == null ? null : fModel.getNodes()) ;
//	}
	
	private void fillToolbar() {
//		ZoomContributionViewItem toolbarZoomContributionViewItem = new ZoomContributionViewItem(this);
//		IToolBarManager tbm = getViewSite().getActionBars().getToolBarManager() ;
//		tbm.add(toolbarZoomContributionViewItem) ;
	}

	@Override
	public void init(IViewSite site) throws PartInitException {
		super.init(site);
	}
	
	public void widgetDefaultSelected(SelectionEvent e) {
		fTabFolder.setSelection(fConfigTab) ;
	}

	public void widgetSelected(SelectionEvent e) {
		fTabFolder.setSelection(fConfigTab) ;
	}
	
	public void setFocus() {
		fTabFolder.setSelection(fConfigTab) ;
	}

	public AbstractZoomableViewer getZoomableViewer() {
		return fGraphViewer ;
	}

	public void setTarget(DiagModel model, IDiagModelFactory factory) {
		fModel = model ;
		fModelFactory = factory ;
		fGraphViewer.setInput(fModel.getNodes()) ;
	}
	
}




