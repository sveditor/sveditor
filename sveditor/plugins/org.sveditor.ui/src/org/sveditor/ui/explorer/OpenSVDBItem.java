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
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.sveditor.ui.explorer;

import java.util.List;

import org.sveditor.ui.SVUiPlugin;
import org.sveditor.ui.editor.SVEditor;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.Path;
import org.sveditor.core.db.ISVDBChildItem;
import org.sveditor.core.db.ISVDBItemBase;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBItem;
import org.sveditor.core.db.index.SVDBDeclCacheItem;
import org.sveditor.core.log.LogFactory;
import org.sveditor.core.log.LogHandle;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IActionBars;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IEditorRegistry;
import org.eclipse.ui.IURIEditorInput;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.actions.SelectionListenerAction;
import org.eclipse.ui.ide.FileStoreEditorInput;
import org.eclipse.ui.navigator.CommonActionProvider;
import org.eclipse.ui.navigator.ICommonActionConstants;
import org.eclipse.ui.navigator.ICommonActionExtensionSite;
import org.eclipse.ui.part.FileEditorInput;

public class OpenSVDBItem extends CommonActionProvider {
	private OpenItemAction			fOpenItem;
	private static LogHandle		fLog;
	
	static {
		fLog = LogFactory.getLogHandle("OpenSVDBItem");
	}

	@Override
	public void init(ICommonActionExtensionSite site) {
		super.init(site);
		fOpenItem = new OpenItemAction();
	}

	@Override
	public void fillContextMenu(IMenuManager menu) {
		menu.add(fOpenItem);

		fOpenItem.selectionChanged(
				(IStructuredSelection)getContext().getSelection());
				
		super.fillContextMenu(menu);
	}
	
	@Override
	public void fillActionBars(IActionBars actionBars) {
		super.fillActionBars(actionBars);
		actionBars.setGlobalActionHandler(ICommonActionConstants.OPEN, 
				fOpenItem);
		
		fOpenItem.selectionChanged(
				(IStructuredSelection)getContext().getSelection());
	}



	private class OpenItemAction extends SelectionListenerAction {
		
		public OpenItemAction() {
			super("Open");
		}

		@Override
		@SuppressWarnings("unchecked")
		public void run() {
			super.run();
			
			for (Object o : (List<Object>)getSelectedNonResources()) {
				IEditorPart ed_f = null;
				ISVDBItemBase it = null;
				
				if (o instanceof IAdaptable) {
					Object t = ((IAdaptable)o).getAdapter(SVDBDeclCacheItem.class);
					if (t == null) {
						t = ((IAdaptable)o).getAdapter(ISVDBItemBase.class);
					}
					
					if (t != null) {
						o = t;
					}
				}
				
				if (o instanceof SVDBDeclCacheItem) {
					it = ((SVDBDeclCacheItem)o).getSVDBItem();
				} else if (o instanceof ISVDBItemBase) {
					it = (ISVDBItemBase)o;
				}
				
				if (it != null) {
					ed_f = openEditor(it);
				}
				
				if (ed_f != null) {
					if (ed_f instanceof SVEditor) {
						((SVEditor)ed_f).setSelection(it, true);
					} else {
						fLog.enter("Editor for \"" + SVDBItem.getName(it) + 
								"\" is not an SVEditor: " + 
						ed_f.getClass().getName());
					}
				}
			}
		}
		
		private IEditorPart openEditor(ISVDBItemBase it) {
			IEditorPart ret = null;
			ISVDBChildItem p = (ISVDBChildItem)it;
			IFile f = null;
			// Find the file that this item belongs to
			
			while (p != null && !(p instanceof SVDBFile)) {
				p = p.getParent();
			}
			
			if (p != null) {
				String file = ((SVDBFile)p).getFilePath();
				IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();
				
				if (file.startsWith("${workspace_loc}")) {
					file = file.substring("${workspace_loc}".length());
				}
				String leaf = ((SVDBFile)p).getName();
				Path   path = new Path(file);
				f = root.getFile(new Path(file));

				getActionSite().getViewSite().getShell();
				IWorkbench wb = PlatformUI.getWorkbench();
				IWorkbenchWindow w = wb.getActiveWorkbenchWindow();

				for (IWorkbenchPage page : w.getPages()) {
					for (IEditorReference ed_r : page.getEditorReferences()) {
						String id = ed_r.getId();
						
						if (!id.equals(SVUiPlugin.PLUGIN_ID + ".editor")) {
							continue;
						}
						IEditorInput in = null;
						
						try {
							in = ed_r.getEditorInput();
						} catch (PartInitException e) {
							e.printStackTrace();
						}
						
						if (in instanceof FileEditorInput) {
							FileEditorInput in_f = (FileEditorInput)in;
							if (in_f.getPath().equals(path)) {
								ret = ed_r.getEditor(true);
								break;
							}
						} else if (in instanceof IURIEditorInput) {
							IURIEditorInput in_u = (IURIEditorInput)in;
							if (in_u.getURI().equals(path)) {
								ret = ed_r.getEditor(true);
								break;
							}
						}
					}
					
					if (ret != null) {
						break;
					}
				}
				
				if (ret == null) {
					w = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
					IEditorRegistry rgy = PlatformUI.getWorkbench().getEditorRegistry();
					IEditorDescriptor desc = rgy.getDefaultEditor(leaf);

					try {
						if (f != null && f.exists()) {
							ret = w.getActivePage().openEditor(
									new FileEditorInput(f),	desc.getId());
						} else if (file.startsWith("plugin:")) {
							// Use Plugin file store
						} else {
							// Use local filesystem
							IFileStore fs = EFS.getLocalFileSystem().getStore(new Path(file));
							ret = w.getActivePage().openEditor(
									new FileStoreEditorInput(fs), desc.getId());
						}
					} catch (PartInitException e) {
						e.printStackTrace();
					}
				}
			}
			
			return ret;
		}
	}
}
