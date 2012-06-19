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

import java.util.HashSet;
import java.util.Set;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.diagrams.DiagModel;
import net.sf.sveditor.core.diagrams.DiagNode;
import net.sf.sveditor.core.diagrams.IDiagModelFactory;
import net.sf.sveditor.ui.SVDBIconUtils;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.views.diagram.contributions.NewDiagramForClassContributionItem;
import net.sf.sveditor.ui.views.diagram.contributions.NewDiagramForClassHandler;

import org.eclipse.draw2d.FanRouter;
import org.eclipse.draw2d.Graphics;
import org.eclipse.draw2d.IFigure;
import org.eclipse.draw2d.ManhattanConnectionRouter;
import org.eclipse.draw2d.SWTGraphics;
import org.eclipse.draw2d.ScalableFigure;
import org.eclipse.draw2d.geometry.Rectangle;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IBaseLabelProvider;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.events.MouseEvent;
import org.eclipse.swt.events.MouseListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageData;
import org.eclipse.swt.graphics.ImageLoader;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.zest.core.viewers.AbstractZoomableViewer;
import org.eclipse.zest.core.viewers.GraphViewer;
import org.eclipse.zest.core.viewers.IZoomableWorkbenchPart;
import org.eclipse.zest.core.viewers.ZoomContributionViewItem;
import org.eclipse.zest.core.widgets.CGraphNode;
import org.eclipse.zest.core.widgets.Graph;
import org.eclipse.zest.layouts.LayoutStyles;
import org.eclipse.zest.layouts.algorithms.GridLayoutAlgorithm;
import org.eclipse.zest.layouts.algorithms.RadialLayoutAlgorithm;
import org.eclipse.zest.layouts.algorithms.TreeLayoutAlgorithm;


public class SVDiagramView extends ViewPart implements SelectionListener, IZoomableWorkbenchPart {
	
	private GraphViewer fGraphViewer ;
	private DiagModel fModel ;
	@SuppressWarnings("unused")
	private IDiagModelFactory fModelFactory ;
	private CTabItem fConfigTab ;
	private CTabFolder fTabFolder ;
	private IDiagLabelProviderConfig fDiagLabelProvider ;
	private NewDiagramForClassHandler fNewDiagramForClassHandler ;
	private NewDiagramForClassContributionItem fNewDiagramForClassContributionItem ;
	
	@SuppressWarnings("unused")
	private double [] fZoomLevels = { 0.25,0.75, 1.0 } ;
	
	public GraphViewer getGraphViewer() {
		return fGraphViewer ;
	}
	
	@Override
	public void createPartControl(Composite parent) {
		
		GridLayout gl = new GridLayout() ;
		
		gl.numColumns = 2 ;
		parent.setLayout(gl) ;
		
		createGraphViewer(parent) ;
		createTabFolder(parent) ;		
		createContextMenu() ;
		createContributions() ;
		
		//
		//
		//
		
		ZoomContributionViewItem toolbarZoomContributionViewItem = new ZoomContributionViewItem(this);
		IActionBars bars = getViewSite().getActionBars();
		bars.getMenuManager().add(toolbarZoomContributionViewItem);
//		fGraphViewer.getGraphControl().getZoomManager().setZoomLevels(fZoomLevels) ; // TODO: Zest 2.0
		
		//
		//
		//
//		fGraphViewer.setLayoutAlgorithm(new RadialLayoutAlgorithm(), false) ; // TODO: Zest 2.0
		fGraphViewer.setLayoutAlgorithm(new RadialLayoutAlgorithm(LayoutStyles.NO_LAYOUT_NODE_RESIZING), false) ;
		
		fTabFolder.setSelection(fConfigTab) ;
		
	}

    private void createContextMenu() {
     MenuManager menuMgr = new MenuManager("#PopupMenu") ;
        menuMgr.setRemoveAllWhenShown(true) ;
        menuMgr.addMenuListener(new IMenuListener() {
                public void menuAboutToShow(IMenuManager mgr) {
                        SVDiagramView.this.fillContextMenu(mgr);
                }
        }) ;
        // Create menu.
        Menu menu = menuMgr.createContextMenu(fGraphViewer.getControl()) ;
        fGraphViewer.getControl().setMenu(menu) ;
    }

	protected void fillContextMenu(IMenuManager mgr) {
		mgr.add(fNewDiagramForClassContributionItem) ;
		mgr.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS)) ;
	}
	private void createContributions() {
		fNewDiagramForClassHandler = new NewDiagramForClassHandler() ;
		fNewDiagramForClassContributionItem = new NewDiagramForClassContributionItem(this, fNewDiagramForClassHandler) ;
	}

	private void createGraphViewer(Composite parent) {
		GridData gd;
		fGraphViewer = new GraphViewer(parent, SWT.BORDER) ;
		fDiagLabelProvider = new DiagLabelProvider() ;
		fGraphViewer.setContentProvider(new DiagContentProvider()) ;
		fGraphViewer.setLabelProvider((IBaseLabelProvider)fDiagLabelProvider) ;
		fGraphViewer.setInput(fModel == null ? null : fModel.getNodes()) ;
		
		gd = new GridData() ; 
		gd.grabExcessVerticalSpace = true ;
		gd.grabExcessHorizontalSpace = true ;
		gd.horizontalAlignment = GridData.FILL ;
		gd.verticalAlignment = GridData.FILL ;
		fGraphViewer.getControl().setLayoutData(gd) ;
	}

	private void createTabFolder(Composite parent) {
		GridData gd;
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
		
		createLayoutGroup() ;
//		createRoutingGroup() ;  // TODO: Zest 2.0
		createClassDetailsGroup() ;
		createToolBarItems(parent) ;
		createListeners() ;
	}

	private void createListeners() {
		
		fGraphViewer.addDoubleClickListener(new IDoubleClickListener() {
			public void doubleClick(DoubleClickEvent event) {
				if(event.getSelection().isEmpty()) return ;
				IStructuredSelection sel = (IStructuredSelection)event.getSelection();
				if (sel.getFirstElement() instanceof DiagNode) {
					DiagNode dn = (DiagNode)sel.getFirstElement() ;
					try {
						SVEditorUtil.openEditor(dn.getSVDBItem()) ;
					} catch (PartInitException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}				
			}
		}) ;
		
		fGraphViewer.getGraphControl().addMouseListener(new MouseListener() {
			public void mouseUp(MouseEvent e) { }
			public void mouseDown(MouseEvent e) {
				// If mouse button pressed NOT on a class figure, undo any selection
				IFigure figure = fGraphViewer.getGraphControl().getFigureAt(e.x, e.y) ;
				if(figure == null) {
					// DeSelect all the selected nodes
					Set<DiagNode> nodesChanged = new HashSet<DiagNode>() ;
					for(Object item: fGraphViewer.getGraphControl().getGraph().getSelection()) {
						if(!(item instanceof CGraphNode)) { continue ; }
						CGraphNode graphNode = (CGraphNode)item ;
						if(!(graphNode.getData() instanceof DiagNode)) { continue ; }
						DiagNode dNode = (DiagNode)graphNode.getData() ;
						dNode.setSelected(false) ;
						nodesChanged.add(dNode) ;
					}
					// Refresh the view. This might get slow with large diagrams.
					if(nodesChanged.size() != 0) {
						fGraphViewer.refresh();
					}
					fGraphViewer.getGraphControl().getGraph().setSelection(null) ;
				}
			}
			public void mouseDoubleClick(MouseEvent e) { }
		}) ;
		
		
		fGraphViewer.getGraphControl().addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				if(!(e.widget instanceof Graph)) {
					return ;
				}
				Graph graph = (Graph)e.widget ;
				Set<DiagNode> nodesChanged = new HashSet<DiagNode>() ;
				// Deselect all nodes
				for(Object obj: graph.getNodes()) {
					if(!(obj instanceof CGraphNode)) { continue ; }
					CGraphNode graphNode = (CGraphNode)obj ;
					if(!(graphNode.getData() instanceof DiagNode)) { continue ; }
					DiagNode dNode = (DiagNode)graphNode.getData() ;
					if(dNode.getSelected()) {
						dNode.setSelected(false) ;
						nodesChanged.add(dNode) ;
					}
				}
				// Select all the selected nodes
				for(Object item: fGraphViewer.getGraphControl().getGraph().getSelection()) {
					if(!(item instanceof CGraphNode)) { continue ; }
					CGraphNode graphNode = (CGraphNode)item ;
					if(!(graphNode.getData() instanceof DiagNode)) { continue ; }
					DiagNode dNode = (DiagNode)graphNode.getData() ;
					dNode.setSelected(true) ;
					nodesChanged.add(dNode) ;
				}
				// Refresh the view. This might get slow with large diagrams.
				if(nodesChanged.size() != 0) {
					fGraphViewer.refresh();
				}
			}
		}) ;
		
	}

	private void createToolBarItems(Composite parent) {
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
					ScalableFigure figure = fGraphViewer.getGraphControl().getRootLayer() ;
					Rectangle bounds = figure.getBounds() ;
					Control srcCanvas = fGraphViewer.getGraphControl() ;
					GC srcGC = new GC(srcCanvas) ;
					Image destImg = new Image(null, bounds.width, bounds.height) ;
					GC destImgGC = new GC(destImg) ;
					destImgGC.setBackground(srcGC.getBackground()) ;
					destImgGC.setForeground(srcGC.getForeground()) ;
					destImgGC.setFont(srcGC.getFont()) ;
					destImgGC.setLineStyle(srcGC.getLineStyle()) ;
					destImgGC.setLineWidth(srcGC.getLineWidth()) ;
					Graphics dstImgGraphics = new SWTGraphics(destImgGC) ;
					figure.paint(dstImgGraphics) ;
					ImageLoader imgLoader = new ImageLoader() ;
					imgLoader.data = new ImageData[] { destImg.getImageData() } ;
					imgLoader.save(selected, SWT.IMAGE_PNG) ;
					destImg.dispose() ;
					destImgGC.dispose() ;
				}
			} }) ;
	}

	private void createClassDetailsGroup() {
		Group group;
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
	}

	@SuppressWarnings("unused")
	private void createRoutingGroup() {
		Group group;
		group = new Group((Composite)fConfigTab.getControl(), SWT.NONE) ;
		group.setLayoutData(new GridData(GridData.FILL_HORIZONTAL)) ;
		group.setLayout(new RowLayout(SWT.VERTICAL)) ;
		group.setText("Connection Routing") ;
		Button routingButtons[] = new Button[2] ;
		routingButtons[0] = new Button(group, SWT.RADIO) ;
		routingButtons[0].setText("Manhattan (Default)") ;
		routingButtons[0].setSelection(true) ;
		fDiagLabelProvider.setSVDiagRouter(new ManhattanConnectionRouter()) ;
		routingButtons[0].addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fDiagLabelProvider.setSVDiagRouter(new ManhattanConnectionRouter()) ;
				fGraphViewer.setInput(fModel.getNodes()) ;
			}
		});
		routingButtons[1] = new Button(group, SWT.RADIO) ;
		routingButtons[1].setText("Fan") ;
		routingButtons[1].addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
				fDiagLabelProvider.setSVDiagRouter(new FanRouter()) ;
				fGraphViewer.setInput(fModel.getNodes()) ;
			}
		});
	}

	private void createLayoutGroup() {
		Group group;
		group = new Group((Composite)fConfigTab.getControl(), SWT.NONE) ;
		group.setLayoutData(new GridData(GridData.FILL_HORIZONTAL)) ;
		group.setLayout(new RowLayout(SWT.VERTICAL)) ;
		group.setText("Layout") ;
		Button layoutRadios[] = new Button[3] ;
		layoutRadios[0] = new Button(group, SWT.RADIO) ;
		layoutRadios[0].setText("Grid (Default)") ;
		layoutRadios[0].setSelection(true) ;
		layoutRadios[0].addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
//				fGraphViewer.setLayoutAlgorithm(new GridLayoutAlgorithm()) ; // TODO: Zest 2.0
				fGraphViewer.setLayoutAlgorithm(new GridLayoutAlgorithm(LayoutStyles.NO_LAYOUT_NODE_RESIZING)) ;
				fGraphViewer.applyLayout() ;
			}
		});
		layoutRadios[1] = new Button(group, SWT.RADIO) ;
		layoutRadios[1].setText("Radial") ;
		layoutRadios[1].addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
//				fGraphViewer.setLayoutAlgorithm(new RadialLayoutAlgorithm()) ; // TODO: Zest 2.0
				fGraphViewer.setLayoutAlgorithm(new RadialLayoutAlgorithm(LayoutStyles.NO_LAYOUT_NODE_RESIZING)) ;
				fGraphViewer.applyLayout() ;
			}
		});
		layoutRadios[2] = new Button(group, SWT.RADIO) ;
		layoutRadios[2].setText("Tree") ;
		layoutRadios[2].addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(SelectionEvent e) {
//				fGraphViewer.setLayoutAlgorithm(new TreeLayoutAlgorithm()) ; // TODO: Zest 2.0
				fGraphViewer.setLayoutAlgorithm(new TreeLayoutAlgorithm(LayoutStyles.NO_LAYOUT_NODE_RESIZING)) ;
				fGraphViewer.applyLayout() ;
			}
		});
	}
	
	private void updateInputNoLayout() {
		fGraphViewer.setLayoutAlgorithm(new LeaveEmBeLayoutAlgoritm(SWT.NONE)) ;
		fGraphViewer.setInput(fModel.getNodes()) ;
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

	public void setTarget(DiagModel model, IDiagModelFactory factory, ISVDBIndex index) {
		if(model == null || factory == null || index == null) { return ; }
		fModel = model ;
		fModelFactory = factory ;
		fNewDiagramForClassHandler.setSVDBIndex(index) ;
		fGraphViewer.setInput(fModel.getNodes()) ;
//		fGraphViewer.setLayoutAlgorithm(new GridLayoutAlgorithm()) ; // TODO: Zest 2.0
		fGraphViewer.setLayoutAlgorithm(new GridLayoutAlgorithm(LayoutStyles.NO_LAYOUT_NODE_RESIZING)) ;
	}
	
	public void setViewState(int state) {
		IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		int currentState = page.getPartState(page.getReference(this));
		if(currentState != state) {
			page.activate(this);
			page.setPartState(page.getReference(this), state);
		}
	}

	
}




