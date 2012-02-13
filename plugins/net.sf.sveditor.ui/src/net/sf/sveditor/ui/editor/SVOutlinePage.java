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

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBChangeListener;
import net.sf.sveditor.ui.SVDBIconUtils;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;
import net.sf.sveditor.ui.svcp.SVDBDecoratingLabelProvider;
import net.sf.sveditor.ui.svcp.SVDBDefaultContentFilter;
import net.sf.sveditor.ui.svcp.SVTreeContentProvider;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IElementComparer;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.part.IPageSite;
import org.eclipse.ui.part.IShowInTarget;
import org.eclipse.ui.part.ShowInContext;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

public class SVOutlinePage extends ContentOutlinePage 
	implements IShowInTarget, IAdaptable, 
			Runnable, ISVDBChangeListener {
	private SVTreeContentProvider		fContentProvider;
	private SVEditor					fEditor;
	private boolean						fIgnoreSelectionChange = false;
	private ISVDBItemBase				fLastSelection;
	private Action                      ToggleAssign;
	private Action                      ToggleAlways;
	private Action                      ToggleDefines;
	private Action                      ToggleInitial;
	private Action                      ToggleGenerate;
	private Action                      ToggleVariables;
	private Action                      ToggleModuleInstances;
	private Action                      ToggleInclude;
	private Action                      ToggleTaskFunction;
	private SVDBDefaultContentFilter    DefaultContentFilter;
	
	public SVOutlinePage(SVEditor editor) {
		fEditor = editor;
		fContentProvider = new SVTreeContentProvider();
	}
	
	public void createControl(Composite parent) {
		super.createControl(parent);
		
		fContentProvider = new SVTreeContentProvider();
		DefaultContentFilter = new SVDBDefaultContentFilter();

		
		// Set up the preferences from the preference store
		DefaultContentFilter.HideAlwaysStatements    (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_ALWAYS_BLOCKS));
		DefaultContentFilter.HideAssignStatements    (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_ASSIGN_STATEMENTS));
		DefaultContentFilter.HideDefineStatements    (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_DEFINE_STATEMENTS));
		DefaultContentFilter.HideGenerateBlocks      (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_GENERATE_BLOCKS));
		DefaultContentFilter.HideIncludeFiles        (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_INCLUDE_FILES));
		DefaultContentFilter.HideInitialBlocks       (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_INITIAL_BLOCKS));
		DefaultContentFilter.HideModuleInstances     (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_MODULE_INSTANCES));
		DefaultContentFilter.HideTaskFunctions       (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_TASK_FUNCTION_DECLARATIONS));
		DefaultContentFilter.HideVariableDeclarations(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_SIGNAL_DECLARATIONS));
	
		
		getTreeViewer().setContentProvider(fContentProvider);
		getTreeViewer().addFilter(DefaultContentFilter);
		getTreeViewer().setLabelProvider(
				new SVDBDecoratingLabelProvider(new SVTreeLabelProvider()));
		getTreeViewer().setComparer(new IElementComparer() {
			public int hashCode(Object element) {
				return element.hashCode();
			}
			
			public boolean equals(Object a, Object b) {
				if (a instanceof ISVDBItemBase && b instanceof ISVDBItemBase) {
					return ((ISVDBItemBase)a).equals((ISVDBItemBase)b, true);
				} else {
					return a.equals(b);
				}
			}
		});
		
		getTreeViewer().setInput(fEditor.getSVDBFile());
		
		getTreeViewer().getControl().getDisplay().asyncExec(this);
		/*
		getTreeViewer().getControl().addListener(SWT.MouseDown, 
				new Listener() {
					
					@Override
					public void handleEvent(Event event) {
						System.out.println("Mouse: " + event.button + " " + event.type);
					}
				});
		 */
		
		getTreeViewer().addSelectionChangedListener(fSelectionListener);
		getTreeViewer().setAutoExpandLevel(TreeViewer.ALL_LEVELS);
		
	}

	
	public void SVDBFileChanged(SVDBFile file, List<SVDBItem> adds,
			List<SVDBItem> removes, List<SVDBItem> changes) {
		if (file.getFilePath().equals(fEditor.getFilePath())) {
			if (getTreeViewer() != null && !getTreeViewer().getControl().isDisposed()) {
				Display.getDefault().asyncExec(this);
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

	@SuppressWarnings("rawtypes")
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
				if (fIgnoreSelectionChange) {
					return;
				}
				
				removeSelectionChangedListener(this);
				
				if (event.getSelection() instanceof StructuredSelection) {
					StructuredSelection sel = (StructuredSelection)event.getSelection();
					if (sel.getFirstElement() instanceof ISVDBItemBase) {
						ISVDBItemBase it = (ISVDBItemBase)sel.getFirstElement();
						
						if (fLastSelection == null || !fLastSelection.equals(it, true)) {
							fEditor.setSelection(it, false);
							fLastSelection = it;
						}
					}
				}
				
				addSelectionChangedListener(this);
			}
	};
	
	public void createActions() {
	}
	
	@Override
	public void init(IPageSite pageSite) {
		super.init(pageSite);
		
		// Add button to toggle assign statements on and off
		ToggleAssign = new Action("Assign", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleAssign.setChecked(DefaultContentFilter.ToggleAssignStatements());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_ASSIGN_STATEMENTS, ToggleAssign.isChecked());
				refresh();
			}
		};
		ToggleAssign.setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.Assign));
		pageSite.getActionBars().getToolBarManager().add(ToggleAssign);
		
		// Add button to toggle Always statements on and off
		ToggleAlways = new Action("Always", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleAlways.setChecked(DefaultContentFilter.ToggleAlwaysStatements());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_ALWAYS_BLOCKS, ToggleAlways.isChecked());
				refresh();
			}
		};
		ToggleAlways.setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.AlwaysStmt));
		pageSite.getActionBars().getToolBarManager().add(ToggleAlways);
		
		// Add button to toggle `define statements on and off
		ToggleDefines = new Action("`define", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleDefines.setChecked(DefaultContentFilter.ToggleDefineStatements());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_DEFINE_STATEMENTS, ToggleDefines.isChecked());
				refresh();
			}
		};
		ToggleDefines.setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.MacroDef));
		pageSite.getActionBars().getToolBarManager().add(ToggleDefines);
		
		// Add button to toggle Initial statements on and off
		ToggleInitial= new Action("Initial", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleInitial.setChecked(DefaultContentFilter.ToggleInitialBlocks());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_INITIAL_BLOCKS, ToggleInitial.isChecked());
				refresh();
			}
		};
		ToggleInitial.setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.InitialStmt));
		pageSite.getActionBars().getToolBarManager().add(ToggleInitial);
		
		// Add button to toggle Generate statements on and off
		ToggleGenerate = new Action("Generate", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleGenerate.setChecked(DefaultContentFilter.ToggleGenerateBlocks());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_GENERATE_BLOCKS, ToggleGenerate.isChecked());
				refresh();
			}
		};
		ToggleGenerate .setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.GenerateBlock));
		pageSite.getActionBars().getToolBarManager().add(ToggleGenerate);
		
		// Add button to toggle Variables statements on and off
		ToggleVariables= new Action("Signals", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleVariables.setChecked(DefaultContentFilter.ToggleVariableDeclarations());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_SIGNAL_DECLARATIONS, ToggleVariables.isChecked());
				refresh();
			}
		};
		ToggleVariables.setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.VarDeclItem));
		pageSite.getActionBars().getToolBarManager().add(ToggleVariables);
		
		// Add button to toggle Module Instances statements on and off
		ToggleModuleInstances = new Action("Module Instances", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleModuleInstances.setChecked(DefaultContentFilter.ToggleModuleInstances());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_MODULE_INSTANCES, ToggleModuleInstances.isChecked());
				refresh();
			}
		};
		ToggleModuleInstances.setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.ModIfcInst));
		pageSite.getActionBars().getToolBarManager().add(ToggleModuleInstances);
		
		// Add button to toggle Include files statements on and off
		ToggleInclude= new Action("Include/Import", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleInclude.setChecked(DefaultContentFilter.ToggleIncludeFiles());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_INCLUDE_FILES, ToggleInclude.isChecked());
				refresh();
			}
		};
		ToggleInclude.setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.Include));
		pageSite.getActionBars().getToolBarManager().add(ToggleInclude);
	
		// Add button to toggle Task / Function statements on and off
		ToggleTaskFunction = new Action("Task/Function", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleTaskFunction.setChecked(DefaultContentFilter.ToggleTaskFunctions());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_TASK_FUNCTION_DECLARATIONS, ToggleTaskFunction.isChecked());
				refresh();
			}
		};
		ToggleTaskFunction.setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.Task));
		pageSite.getActionBars().getToolBarManager().add(ToggleTaskFunction);
		
		// Set up which of the content filters are enabled
		// Now, format the new addition if auto-indent is enabled
		
		ToggleAlways         .setChecked(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_ALWAYS_BLOCKS));
		ToggleAssign         .setChecked(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_ASSIGN_STATEMENTS));
		ToggleDefines        .setChecked(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_DEFINE_STATEMENTS));
		ToggleGenerate       .setChecked(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_GENERATE_BLOCKS));
		ToggleInclude        .setChecked(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_INCLUDE_FILES));
		ToggleInitial        .setChecked(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_INITIAL_BLOCKS));
		ToggleModuleInstances.setChecked(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_MODULE_INSTANCES));
		ToggleTaskFunction   .setChecked(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_TASK_FUNCTION_DECLARATIONS));
		ToggleVariables      .setChecked(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_SIGNAL_DECLARATIONS));
	
	}
}