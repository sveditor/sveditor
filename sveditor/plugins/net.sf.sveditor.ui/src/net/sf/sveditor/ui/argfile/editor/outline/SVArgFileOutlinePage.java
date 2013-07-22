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


package net.sf.sveditor.ui.argfile.editor.outline;

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
import net.sf.sveditor.core.db.index.ISVDBChangeListener;
import net.sf.sveditor.core.db.index.SVDBFilePath;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.SVEditorUtil;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.argfile.editor.SVArgFileEditor;
import net.sf.sveditor.ui.svcp.SVDBDefaultContentFilter;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.action.Action;
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

public class SVArgFileOutlinePage extends ContentOutlinePage 
	implements IShowInTarget, IAdaptable, 
			Runnable, ISVDBChangeListener, ILogLevelListener {
	private SVArgFileOutlineContent				fContent;
	private SVArgFileOutlineContentProvider		fContentProvider;
	private SVArgFileEditor						fEditor;
	private boolean								fIgnoreSelectionChange = false;
	private ISVDBItemBase						fLastSelection;
	private SVDBDefaultContentFilter			DefaultContentFilter;
	private ViewerComparator					ViewerComapartor;
	private LogHandle							fLog;
	private boolean								fDebugEn;
	private SortAction							ToggleSort;
	
	public SVArgFileOutlinePage(SVArgFileEditor editor) {
		fEditor = editor;
		fContentProvider = new SVArgFileOutlineContentProvider();
		fContent = new SVArgFileOutlineContent(new SVDBFile(""), null);
		
		fLog = LogFactory.getLogHandle("SVArgFileOutlinePage");
		fDebugEn = fLog.isEnabled();
	}
	
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = handle.isEnabled();
	}

	public ITreeContentProvider getContentProvider() {
		return fContentProvider;
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

		fContentProvider = new SVArgFileOutlineContentProvider();
		DefaultContentFilter = new SVDBDefaultContentFilter();
		ViewerComapartor     = new ViewerComparator();

		
		// Set up the preferences from the preference store
		getTreeViewer().setContentProvider(fContentProvider);
		getTreeViewer().addFilter(DefaultContentFilter);
		// Check whether we have sorting enabled or not
		/*
		if (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVArgFileEditorPrefsConstants.P_OUTLINE_SORT))  {
			getTreeViewer().setComparator(ViewerComapartor);
		} else {
		 */
			getTreeViewer().setComparator(null);
//		}
		getTreeViewer().setLabelProvider(new SVArgFileOutlineLabelProvider());
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

	
	public void SVDBFileChanged(SVDBFile file, List<SVDBItem> adds,
			List<SVDBItem> removes, List<SVDBItem> changes) {
		/** TODO:
		if (file.getFilePath().equals(fEditor.getFilePath())) {
			if (getTreeViewer() != null && !getTreeViewer().getControl().isDisposed()) {
				Display.getDefault().asyncExec(this);
			}
		}
		 */
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
			
			fContent = new SVArgFileOutlineContent(fEditor.getSVDBFile(), file_path);
			
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
							ISVDBItemBase sel_t = (ISVDBItemBase)target_path.get(target_path.size()-1);
							new_sel_l.add(sel_t);
						}
					} else if (sel_it instanceof SVDBFilePath) {
						new_sel_l.add(fContent.getFilePath());
					} else if (sel_it instanceof Tuple) {
						Tuple<SVDBFileTree, ISVDBItemBase> t = (Tuple<SVDBFileTree, ISVDBItemBase>)sel_it;
						
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
								fLog.debug("Setting SVArgFileEditor selection: " + SVDBItem.getName(it) + " @ " + 
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
			/** TODO:
			if (SVUiPlugin.getDefault().getPreferenceStore().getBoolean(SVArgFileEditorPrefsConstants.P_OUTLINE_SORT))  {
				new_value = false;
			}
			// Update the preferences
			SVUiPlugin.getDefault().getPreferenceStore().setValue(SVArgFileEditorPrefsConstants.P_OUTLINE_SORT, new_value);
			// Update the value
			ToggleSort.setChecked(new_value);
			 */
			
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
		/** TODO:
		 */
		
		// Set up which of the content filters are enabled
		// Now, format the new addition if auto-indent is enabled
//		IPreferenceStore ps = SVUiPlugin.getDefault().getPreferenceStore();
	}
}