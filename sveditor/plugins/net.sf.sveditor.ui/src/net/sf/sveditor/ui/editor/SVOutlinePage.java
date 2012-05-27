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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.index.ISVDBChangeListener;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.ui.SVDBIconUtils;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;
import net.sf.sveditor.ui.svcp.SVDBDecoratingLabelProvider;
import net.sf.sveditor.ui.svcp.SVDBDefaultContentFilter;
import net.sf.sveditor.ui.svcp.SVTreeContentProvider;
import net.sf.sveditor.ui.svcp.SVTreeLabelProvider;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.viewers.IElementComparer;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreePath;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.part.IPageSite;
import org.eclipse.ui.part.IShowInTarget;
import org.eclipse.ui.part.ShowInContext;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

public class SVOutlinePage extends ContentOutlinePage 
	implements IShowInTarget, IAdaptable, 
			Runnable, ISVDBChangeListener {
	private SVDBFile					fSVDBFile;
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
	private Action                      ToggleSort;
	private SVDBDefaultContentFilter    DefaultContentFilter;
	private ViewerComparator            ViewerComapartor;
	
	public SVOutlinePage(SVEditor editor) {
		fEditor = editor;
		fContentProvider = new SVTreeContentProvider();
		
		fSVDBFile = new SVDBFile("");
	}
	
	public void createControl(Composite parent) {
		super.createControl(parent);

		fContentProvider = new SVTreeContentProvider();
		DefaultContentFilter = new SVDBDefaultContentFilter();
		ViewerComapartor     = new ViewerComparator();

		
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
		// Check whether we have sorting enabled or not
		if (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SORT))  {
			getTreeViewer().setComparator(ViewerComapartor);
		}
		else  {
			getTreeViewer().setComparator(null);
		}
		getTreeViewer().setLabelProvider(
				new SVDBDecoratingLabelProvider(new SVTreeLabelProvider()));
		getTreeViewer().setComparer(new IElementComparer() {
			public int hashCode(Object element) {
				return element.hashCode();
			}
			
			public boolean equals(Object a, Object b) {
				// Just do a simple compare
				return (a == b);
			}
		});
		
		getTreeViewer().setInput(fSVDBFile);
		
		getTreeViewer().addSelectionChangedListener(fSelectionListener);
		getTreeViewer().setAutoExpandLevel(TreeViewer.ALL_LEVELS);
		
		// Get initial contents
		refresh();
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
			fSVDBFile = fEditor.getSVDBFile();
			
			List<ISVDBItemBase> exp_path_list = getExpansionPaths();
			
			ISelection sel = getTreeViewer().getSelection();
			
			getTreeViewer().setInput(fSVDBFile);
			
			// Apply selection and expansions previously saved
			setExpansionPaths(exp_path_list);
			
			setSavedSelection(sel);
		}
	}
	
	private List<ISVDBItemBase> getExpansionPaths() {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		for (TreePath p : getTreeViewer().getExpandedTreePaths()) {
			Object last_seg_o = p.getLastSegment();
			
			if (last_seg_o instanceof ISVDBItemBase) {
				ret.add((ISVDBItemBase)last_seg_o);
			}
		}

		return ret;
	}
	
	private void setExpansionPaths(List<ISVDBItemBase> exp_paths) {
		List<ISVDBItemBase> path = new ArrayList<ISVDBItemBase>();
		List<ISVDBItemBase> target_path = new ArrayList<ISVDBItemBase>();
		List<TreePath>		exp_tree_paths = new ArrayList<TreePath>();
		
		for (ISVDBItemBase item : exp_paths) {
			path.clear();
			target_path.clear();
			
			// Build the path
			buildFullPath(path, item);
			
			// Find the corresponding path
			lookupPath(fSVDBFile, path.iterator(), target_path);
			
			if (target_path.size() > 0) {
				exp_tree_paths.add(new TreePath(target_path.toArray()));
			}
		}
		
		if (exp_tree_paths.size() > 0) {
			getTreeViewer().setExpandedTreePaths(exp_tree_paths.toArray(
					new TreePath[exp_tree_paths.size()]));
		}
	}
	
	private void buildFullPath(List<ISVDBItemBase> path, ISVDBItemBase leaf) {
		ISVDBItemBase item_tmp = leaf;
		while (item_tmp != null && item_tmp.getType() != SVDBItemType.File) {
			// Don't record the container, since there isn't an
			// identifier to use
			if (!(item_tmp instanceof SVDBVarDeclStmt) &&
					!(item_tmp instanceof SVDBModIfcInst)) {
				path.add(0, item_tmp);
			}
			if (item_tmp instanceof ISVDBChildItem) {
				item_tmp = ((ISVDBChildItem)item_tmp).getParent();
			} else {
				item_tmp = null;
			}
		}
	}
	
	private void setSavedSelection(ISelection sel) {
		fIgnoreSelectionChange = true;
		if (!sel.isEmpty() && sel instanceof IStructuredSelection) {
			List<ISVDBItemBase> path = new ArrayList<ISVDBItemBase>();
			IStructuredSelection ss = (IStructuredSelection)sel;
			List<ISVDBItemBase> new_sel_l = new ArrayList<ISVDBItemBase>();
			List<ISVDBItemBase> target_path = new ArrayList<ISVDBItemBase>();
			
			for (Object sel_it : ss.toList()) {
				if (sel_it instanceof ISVDBItemBase) {
					path.clear();
					target_path.clear();
					buildFullPath(path, (ISVDBItemBase)sel_it);
					
					if (lookupPath(fSVDBFile, path.iterator(), target_path)) {
						ISVDBItemBase sel_t = target_path.get(target_path.size()-1);
						new_sel_l.add(sel_t);
					}
				}
			}
			StructuredSelection new_sel = new StructuredSelection(new_sel_l);
			
			getTreeViewer().setSelection(new_sel);
		}
	}
	
	private boolean lookupPath(
			ISVDBChildParent			scope,
			Iterator<ISVDBItemBase>		path_it,
			List<ISVDBItemBase>			target_path) {
		ISVDBItemBase path_item = path_it.next();
		ISVDBItemBase target_item = null;
		boolean ret = false;
		
		if (!(path_item instanceof ISVDBNamedItem)) {
			// TODO:
			return ret;
		}
		
		ISVDBNamedItem ni = (ISVDBNamedItem)path_item;
		
		for (ISVDBChildItem ci : scope.getChildren()) {
			if (ci instanceof ISVDBNamedItem) {
				ISVDBNamedItem ci_ni = (ISVDBNamedItem)ci;
				if (ni.getName().equals(ci_ni.getName()) &&
						ni.getType() == ci_ni.getType()) {
					target_item = ci;
					break;
				}
			} else if (ci instanceof SVDBVarDeclStmt ||
					ci instanceof SVDBModIfcInst) {
				// instance list
				ISVDBChildParent inst_list = (ISVDBChildParent)ci;
				for (ISVDBChildItem ci_inst : inst_list.getChildren()) {
					ISVDBNamedItem ci_inst_ni = (ISVDBNamedItem)ci_inst;
					if (ni.getName().equals(ci_inst_ni.getName()) &&
							ni.getType() == ci_inst_ni.getType()) {
						target_item = ci_inst;
						break;
					}
				}
				if (target_item != null) {
					break;
				}
			} else {
				// TODO: How to match?
			}
		}
		
		if (target_item != null) {
			target_path.add(target_item);
		}
		
		if (path_it.hasNext() && target_item != null &&
				target_item instanceof ISVDBChildParent) {
			ret = lookupPath((ISVDBChildParent)target_item, path_it, target_path);
		} else if (!path_it.hasNext() && target_item != null) {
			ret = true;
		}
		
		return ret;
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
					fIgnoreSelectionChange = false;
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
	
	private class SortAction extends Action {
		public SortAction() {
			super("sort", Action.AS_CHECK_BOX);
			setImageDescriptor(SVUiPlugin.getImageDescriptor("/icons/elcl16/alphab_sort_co.gif"));
		}
		
		public void run() {
			boolean new_value = true;
			if (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SORT))  {
				new_value = false;
			}
			// Update the preferences
			SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SORT, new_value);
			// Update the value
			ToggleSort.setChecked(new_value);
			// enable or disable the sorter
			if (new_value)  {
				getTreeViewer().setComparator(ViewerComapartor);
			}
			else  {
				getTreeViewer().setComparator(null);
			}
			refresh();
		}
	}
	
	@Override
	public void init(IPageSite pageSite) {
		super.init(pageSite);
		
		// Add button to toggle assign statements on and off
		ToggleSort = new SortAction();
		pageSite.getActionBars().getToolBarManager().add(ToggleSort);
		
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
		IPreferenceStore ps = SVUiPlugin.getDefault().getPreferenceStore();
		ToggleSort           .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SORT));
		ToggleAlways         .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_ALWAYS_BLOCKS));
		ToggleAssign         .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_ASSIGN_STATEMENTS));
		ToggleDefines        .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_DEFINE_STATEMENTS));
		ToggleGenerate       .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_GENERATE_BLOCKS));
		ToggleInclude        .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_INCLUDE_FILES));
		ToggleInitial        .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_INITIAL_BLOCKS));
		ToggleModuleInstances.setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_MODULE_INSTANCES));
		ToggleTaskFunction   .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_TASK_FUNCTION_DECLARATIONS));
		ToggleVariables      .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_SIGNAL_DECLARATIONS));
	}
}