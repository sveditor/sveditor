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


package net.sf.sveditor.ui.explorer;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.ui.SVUiPlugin;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
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
			
			for (SVDBItem it : (List<SVDBItem>)getSelectedNonResources()) {
				System.out.println("Open " + it.getType() + " " + it.getName());
				IEditorPart ed_f = openEditor(it);
				if (ed_f != null) {
					((SVEditor)ed_f).setSelection(it, true);
				}
			}
		}
		
		private IEditorPart openEditor(SVDBItem it) {
			IEditorPart ret = null;
			SVDBItem p = it;
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
						
						System.out.println("Input instanceof " + in.getClass().getName());
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
					System.out.println("Target file: " + f);
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
							System.out.println("Create FileStore from \"" + file + "\" " + fs);
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
