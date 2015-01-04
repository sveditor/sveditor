/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.ui.editor.outline;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcInst;
import net.sf.sveditor.core.db.SVDBModIfcInstItem;
import net.sf.sveditor.core.db.SVDBTypeInfo;
import net.sf.sveditor.core.db.index.ISVDBChangeListener;
import net.sf.sveditor.core.db.index.SVDBFilePath;
import net.sf.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.db.utils.SVDBSearchUtils;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.ui.SVDBIconUtils;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;
import net.sf.sveditor.ui.pref.SVEditorPrefsConstants;
import net.sf.sveditor.ui.svcp.SVDBDefaultContentFilter;
import net.sf.sveditor.ui.svcp.SVTreeContentProvider;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.IElementComparer;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreePath;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.IPageSite;
import org.eclipse.ui.part.IShowInTarget;
import org.eclipse.ui.part.ShowInContext;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

public class SVOutlinePage extends ContentOutlinePage 
	implements IShowInTarget, IAdaptable, 
			Runnable, ISVDBChangeListener, ILogLevelListener {
	private SVOutlineContent			fContent;
	private SVOutlineContentProvider	fContentProvider;
	private SVEditor					fEditor;
	private boolean						fIgnoreSelectionChange = false;
	private ISVDBItemBase				fLastSelection;
	private Action                     ToggleAssign;
	private Action                     ToggleAlways;
	private Action                     ToggleDefines;
	private Action                     ToggleInitial;
	private Action                     ToggleGenerate;
	private Action                     ToggleVariables;
	private Action                     ToggleModuleInstances;
	private Action                     ToggleInclude;
	private Action                     ToggleTaskFunction;
	private Action                     ToggleEnumTypedefs;
	private Action                     ToggleAssertionProperties;
	private Action                     ToggleCoverPointGroupCross;
	private Action                     ToggleConstraints;
	private Action                     ToggleSort;
	private Action						fEnableEditorLinking;
	private SVDBDefaultContentFilter	DefaultContentFilter;
	private ViewerComparator			ViewerComapartor;
	private LogHandle					fLog;
	private boolean						fDebugEn;
	private boolean						fLinkWithEditor = true;
	
	public SVOutlinePage(SVEditor editor) {
		fEditor = editor;
		fContentProvider = new SVOutlineContentProvider();
		
		fContent = new SVOutlineContent(new SVDBFile(""), null);
		
		fLog = LogFactory.getLogHandle("SVOutlinePage");
		fDebugEn = fLog.isEnabled();
		
	}
	
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = handle.isEnabled();
	}



	public ITreeContentProvider getContentProvider() {
		return fContentProvider;
	}
	
	public SVOutlineContent getContent() {
		return fContent;
	}
	
	@Override
	public void setSelection(ISelection selection) {
		if (fDebugEn) {
			fLog.debug("setSelection: " + selection);
		}
		super.setSelection(selection);
	}

	public void createControl(Composite parent) {
		super.createControl(parent);

		fContentProvider = new SVOutlineContentProvider();
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
		DefaultContentFilter.HideEnumTypedefs        (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_ENUM_TYPEDEFS));
		DefaultContentFilter.HideAssertionProperties (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_ASSERTION_PROPERTIES));
		DefaultContentFilter.HideCoverPointGroupCross(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_COVER_POINT_GROUP_CROSS));
		DefaultContentFilter.HideConstraints         (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_CONSTRAINTS));

		getTreeViewer().setContentProvider(fContentProvider);
		getTreeViewer().addFilter(DefaultContentFilter);
		// Check whether we have sorting enabled or not
		if (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVEditorPrefsConstants.P_OUTLINE_SORT))  {
			getTreeViewer().setComparator(ViewerComapartor);
		}
		else  {
			getTreeViewer().setComparator(null);
		}
		getTreeViewer().setLabelProvider(new SVOutlineLabelProvider());
		getTreeViewer().setComparer(new IElementComparer() {
			public int hashCode(Object element) {
				return element.hashCode();
			}
			
			public boolean equals(Object a, Object b) {
				// Just do a simple compare
				return (a == b);
			}
		});
		
		getTreeViewer().setInput(fContent);
		
		getTreeViewer().addSelectionChangedListener(fSelectionListener);
		getTreeViewer().addDoubleClickListener(fDoubleClickListener);
		getTreeViewer().setAutoExpandLevel(TreeViewer.ALL_LEVELS);
		
		// Get initial contents
		refresh();
	}
	
	public void clearIgnoreSelectionChange() {
		if (fDebugEn) {
			fLog.debug("clearIgnoreSelectionChange");
		}
		fIgnoreSelectionChange = false;
	}
	
	public void updateCursorLocation(int offset) {
		IDocument doc = fEditor.getDocument();
		
		int line = -1;
		try {
			line = doc.getLineOfOffset(offset);
		} catch (BadLocationException e) { }
		
		if (line != -1 && fLinkWithEditor) {
			line++;
			// Find element corresponding to line
			
			ISVDBItemBase it = SVDBSearchUtils.findActiveStructItem(
					fEditor.getSVDBFile(), line,
					SVTreeContentProvider.fDoNotRecurseScopes,
					SVTreeContentProvider.fExpandInLineItems,
					SVTreeContentProvider.fIgnoreItems
					);
			
			if (it != null) {
				fIgnoreSelectionChange = true;
				getTreeViewer().reveal(it);
				getTreeViewer().setSelection(new StructuredSelection(it));
				fIgnoreSelectionChange = false;
			}
		}
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
			if (fDebugEn) {
				fLog.debug("refresh: schedule refresh of content");
			}
			Display.getDefault().asyncExec(this);
		}
	}

	public void run() {
		if (getTreeViewer() != null && !getTreeViewer().getControl().isDisposed()) {
			if (fDebugEn) {
				fLog.debug("run: refresh content");
			}
			SVDBFilePath file_path = null;
			List<SVDBFilePath> curr_path = fEditor.getSVDBFilePath();
			
			if (curr_path != null && curr_path.size() > 0) {
				file_path = curr_path.get(0);
			}

			fContent = new SVOutlineContent(fEditor.getSVDBFile(), file_path);
			
			List<Object> exp_path_list = getExpansionPaths();
			
			ISelection sel = getTreeViewer().getSelection();
			
			getTreeViewer().setInput(fContent);
			
			// Apply selection and expansions previously saved
			setExpansionPaths(exp_path_list);
			
			setSavedSelection(sel);
		} else {
			if (fDebugEn) {
				fLog.debug("run: ignore due to page closing");
			}
		}
	}
	
	private List<Object> getExpansionPaths() {
		List<Object> ret = new ArrayList<Object>();
		for (TreePath p : getTreeViewer().getExpandedTreePaths()) {
			Object last_seg_o = p.getLastSegment();
			
			if (last_seg_o instanceof ISVDBItemBase ||
					last_seg_o instanceof Tuple || 
					last_seg_o instanceof SVDBFilePath) {
				ret.add(last_seg_o);
			}
		}

		return ret;
	}
	
	@SuppressWarnings("unchecked")
	private void setExpansionPaths(List<Object> exp_paths) {
		List<Object> path = new ArrayList<Object>();
		List<Object> target_path = new ArrayList<Object>();
		List<TreePath>		exp_tree_paths = new ArrayList<TreePath>();
		
		for (Object item : exp_paths) {
			path.clear();
			target_path.clear();
			
			if (item instanceof Tuple) {
				// Build the path
				Tuple<SVDBFileTree, ISVDBItemBase> t = (Tuple<SVDBFileTree, ISVDBItemBase>)item;
				target_path.add(fContent.getFilePath());
				for (Tuple<SVDBFileTree, ISVDBItemBase> i : fContent.getFilePath().getPath()) {
					if (i.first().getFilePath().equals(t.first().getFilePath())) {
						target_path.add(i);
						break;
					}
				}
				
				if (target_path.size() < 2) {
					target_path.clear();
				}
			} else if (item instanceof SVDBFilePath) {
				target_path.add(fContent.getFilePath());
			} else if (item instanceof ISVDBItemBase) {
				// Build the path
				buildFullPath(path, (ISVDBItemBase)item);
				
				// Find the corresponding path
				lookupPath(fContent.getFile(), path.iterator(), target_path);
			}
	
			// Null path items cause a failure in the TreePath constructor
			if (target_path.contains(null)) {
				continue;
			}
			
			if (target_path.size() > 0) {
				exp_tree_paths.add(new TreePath(target_path.toArray()));
			}
		}
		
		if (exp_tree_paths.size() > 0) {
			getTreeViewer().setExpandedTreePaths(exp_tree_paths.toArray(
					new TreePath[exp_tree_paths.size()]));
		}
	}
	
	private void buildFullPath(List<Object> path, ISVDBItemBase leaf) {
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
	
	@SuppressWarnings("unchecked")
	private void setSavedSelection(ISelection sel) {
		if (fDebugEn) {
			fLog.debug("--> setSavedSelection: set fIgnoreSelectionChange=true");
		}
		fIgnoreSelectionChange = true;
		try {
			if (!sel.isEmpty() && sel instanceof IStructuredSelection) {
				List<Object> path = new ArrayList<Object>();
				IStructuredSelection ss = (IStructuredSelection)sel;
				List<Object> new_sel_l = new ArrayList<Object>();
				List<Object> target_path = new ArrayList<Object>();

				for (Object sel_it : ss.toList()) {
					if (sel_it instanceof ISVDBItemBase) {
						path.clear();
						target_path.clear();
						buildFullPath(path, (ISVDBItemBase)sel_it);

						if (lookupPath(fContent.getFile(), path.iterator(), target_path)) {
							Object sel_t = target_path.get(target_path.size()-1);
							new_sel_l.add(sel_t);
						}
					} else if (sel_it instanceof SVDBFilePath) {
						new_sel_l.add(fContent.getFilePath());
					} else if (sel_it instanceof Tuple) {
						Tuple<SVDBFileTree, ISVDBItemBase> t = (Tuple<SVDBFileTree, ISVDBItemBase>)sel_it;
						
						// See if we can find the old selection
						for (Tuple<SVDBFileTree, ISVDBItemBase> i : fContent.getFilePath().getPath()) {
							if (i.first().getFilePath().equals(t.first().getFilePath())) {
								new_sel_l.add(i);
								break;
							}
						}
					}
				}
				StructuredSelection new_sel = new StructuredSelection(new_sel_l);

				getTreeViewer().setSelection(new_sel);
			}
		} finally {
			fIgnoreSelectionChange = false;
		}
		if (fDebugEn) {
			fLog.debug("<-- setSavedSelection: set fIgnoreSelectionChange=true");
		}
	}
	
	private boolean lookupPath(
			ISVDBChildParent			scope,
			Iterator<Object>			path_it,
			List<Object>				target_path) {
		ISVDBItemBase path_item = (ISVDBItemBase)path_it.next();
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
	
	private IDoubleClickListener fDoubleClickListener =
			new IDoubleClickListener() {
				
				@SuppressWarnings("unchecked")
				public void doubleClick(DoubleClickEvent event) {
					IStructuredSelection sel = (IStructuredSelection)getSelection();
					
					if (sel.getFirstElement() != null && sel.getFirstElement() instanceof Tuple) {
						Tuple<SVDBFileTree, ISVDBItemBase> t = (Tuple<SVDBFileTree, ISVDBItemBase>)sel.getFirstElement();
						
						if (t.second() != null) { // Don't mess with 'this' file
							try {
								SVEditorUtil.openEditor(t.second());
							} catch (PartInitException e) {
								fLog.error("Failed to open editor", e);
							}
						}
					} else if (sel.getFirstElement() != null && sel.getFirstElement() instanceof ISVDBItemBase) {
						ISVDBItemBase it = (ISVDBItemBase)sel.getFirstElement();
						String type_name = null;
						
						if (it.getType() == SVDBItemType.VarDeclItem) {
							SVDBVarDeclItem inst_it = (SVDBVarDeclItem)it;
							SVDBVarDeclStmt stmt = (SVDBVarDeclStmt)inst_it.getParent();
							
							if (stmt != null) {
								type_name = stmt.getTypeName();
							}
						} else if (it.getType() == SVDBItemType.ModIfcInstItem) {
							SVDBModIfcInstItem inst_it = (SVDBModIfcInstItem)it;
							SVDBModIfcInst inst = (SVDBModIfcInst)inst_it.getParent();
						
							if (inst != null) {
								type_name = inst.getTypeName();
							}
						}
						
						if (type_name != null) {
							SVDBFindNamedModIfcClassIfc finder = 
									new SVDBFindNamedModIfcClassIfc(fEditor.getIndexIterator());
							List<ISVDBChildItem> result = finder.findItems(type_name);
							
							if (result != null && result.size() > 0) {
								ISVDBChildItem target = result.get(0);
						
								try {
									SVEditorUtil.openEditor(target);
								} catch (PartInitException e) {
									fLog.error("Failed to open editor", e);
								}
							}
						}
					}
				}
			};
	
	private ISelectionChangedListener fSelectionListener = 
		new ISelectionChangedListener() {

			
			public void selectionChanged(SelectionChangedEvent event) {
				if (fDebugEn) {
					fLog.debug("selectionChanged: " + event.getSelection() + " fIgnoreSelectionChange=" + fIgnoreSelectionChange);
				}
				
				if (fIgnoreSelectionChange) {
					if (fDebugEn) {
						fLog.debug("  Toggle fIgnoreSelectionChange=false and return");
					}
//					fIgnoreSelectionChange = false;
					return;
				}
				
				removeSelectionChangedListener(this);
				
				if (fDebugEn) {
					if (event.getSelection() == null) {
						fLog.debug("  Selection is null");
					} else {
						fLog.debug("  Selection is of type " + event.getSelection().getClass().getName());
					}
				}

				if (event.getSelection() instanceof StructuredSelection) {
					StructuredSelection sel = (StructuredSelection)event.getSelection();
					if (fDebugEn) {
						if (sel.getFirstElement() == null) {
							fLog.debug("  Selection target is null");
						} else {
							fLog.debug("  Selection target is of type " + sel.getFirstElement().getClass().getName());
						}
					}
					if (sel.getFirstElement() instanceof ISVDBItemBase) {
						ISVDBItemBase it = (ISVDBItemBase)sel.getFirstElement();
						
						if (fLastSelection == null || !fLastSelection.equals(it, true)) {
							if (fDebugEn) {
								fLog.debug("Setting SVEditor selection: " + SVDBItem.getName(it) + " @ " + 
										((it.getLocation() != null)?it.getLocation().getLine():-1));
							}
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
		
		// Add button to toggle Enumerated Types & Typedefs statements on and off
		ToggleEnumTypedefs = new Action("Enum/Typedef", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleEnumTypedefs.setChecked(DefaultContentFilter.ToggleEnumTypedefs());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_ENUM_TYPEDEFS, ToggleEnumTypedefs.isChecked());
				refresh();
			}
		};
		ToggleEnumTypedefs.setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.TypedefStmt));
		pageSite.getActionBars().getToolBarManager().add(ToggleEnumTypedefs);
		
		// Add button to toggle Constraints statements on and off
		ToggleConstraints = new Action("Constraints", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleConstraints.setChecked(DefaultContentFilter.ToggleConstraints());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_CONSTRAINTS, ToggleConstraints.isChecked());
				refresh();
			}
		};
		ToggleConstraints.setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.Constraint));
		pageSite.getActionBars().getToolBarManager().add(ToggleConstraints);
		
		// Add button to toggle AssertionProperties statements on and off
		ToggleAssertionProperties = new Action("Assertions/Properties/Sequences", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleAssertionProperties.setChecked(DefaultContentFilter.ToggleAssertionProperties());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_ASSERTION_PROPERTIES, ToggleAssertionProperties.isChecked());
				refresh();
			}
		};
		ToggleAssertionProperties.setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.Property));
		pageSite.getActionBars().getToolBarManager().add(ToggleAssertionProperties);
		
		// Add button to toggle Coverpoint/Groupstatements on and off
		ToggleCoverPointGroupCross= new Action("CoverGroup/CrossCover/CoverPoint", Action.AS_CHECK_BOX) {
			public void run() { 
				ToggleCoverPointGroupCross.setChecked(DefaultContentFilter.ToggleCoverPointGroupCross());
				SVUiPlugin.getDefault().getPreferenceStore().setValue(SVEditorPrefsConstants.P_OUTLINE_SHOW_COVER_POINT_GROUP_CROSS, ToggleCoverPointGroupCross.isChecked());
				refresh();
			}
		};
		ToggleCoverPointGroupCross.setImageDescriptor(SVDBIconUtils.getImageDescriptor(SVDBItemType.Coverpoint));
		pageSite.getActionBars().getToolBarManager().add(ToggleCoverPointGroupCross);
		
		// Set up which of the content filters are enabled
		// Now, format the new addition if auto-indent is enabled
		IPreferenceStore ps = SVUiPlugin.getDefault().getPreferenceStore();
		ToggleSort                .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SORT));
		ToggleAlways              .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_ALWAYS_BLOCKS));
		ToggleAssign              .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_ASSIGN_STATEMENTS));
		ToggleDefines             .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_DEFINE_STATEMENTS));
		ToggleGenerate            .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_GENERATE_BLOCKS));
		ToggleInclude             .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_INCLUDE_FILES));
		ToggleInitial             .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_INITIAL_BLOCKS));
		ToggleModuleInstances     .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_MODULE_INSTANCES));
		ToggleTaskFunction        .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_TASK_FUNCTION_DECLARATIONS));
		ToggleEnumTypedefs        .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_ENUM_TYPEDEFS));
		ToggleAssertionProperties .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_ASSERTION_PROPERTIES));
		ToggleCoverPointGroupCross.setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_COVER_POINT_GROUP_CROSS));
		ToggleConstraints         .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_CONSTRAINTS));
		ToggleVariables           .setChecked(ps.getBoolean(SVEditorPrefsConstants.P_OUTLINE_SHOW_SIGNAL_DECLARATIONS));
	
		fEnableEditorLinking = new Action("Link with Editor", Action.AS_CHECK_BOX) {
			public void run() {
				fLinkWithEditor = isChecked();
				SVUiPlugin.getDefault().getPreferenceStore().setValue(
						SVEditorPrefsConstants.P_OUTLINE_SHOW_SIGNAL_DECLARATIONS, 
						isChecked());
			}
		};
		fEnableEditorLinking.setImageDescriptor(SVUiPlugin.getImageDescriptor("/icons/eview16/synced.gif"));
		fEnableEditorLinking.setChecked(SVUiPlugin.getDefault().getPreferenceStore().getBoolean(
						SVEditorPrefsConstants.P_OUTLINE_SHOW_SIGNAL_DECLARATIONS));
		pageSite.getActionBars().getMenuManager().add(fEnableEditorLinking);
	}
}


