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


package org.eclipse.hdt.sveditor.ui;

import java.io.File;
import java.net.URI;

import org.eclipse.hdt.sveditor.ui.argfile.editor.SVArgFileEditor;
import org.eclipse.hdt.sveditor.ui.editor.SVEditor;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.filesystem.IFileSystem;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.fs.plugin.PluginFileStore;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
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
import org.eclipse.ui.ide.FileStoreEditorInput;
import org.eclipse.ui.part.FileEditorInput;

public class SVEditorUtil {
	
	private static LogHandle				fLog = LogFactory.getLogHandle("SVEditorUtil");
	
	public static IEditorPart openEditor(ISVDBItemBase it) throws PartInitException {
		ISVDBItemBase p = it;
		// Find the file that this item belongs to
		
		String typeName = p.getType().toString() ;
		
		while (p != null && p.getType() != SVDBItemType.File) {
			if (p instanceof ISVDBChildItem) {
				p = ((ISVDBChildItem)p).getParent();
			} else {
				p = null;
				break;
			}
		}
		
		if (p == null) {
			fLog.debug("Failed to find file for type \"" + typeName + "\"");
			return null ;
		}
		
		String file = ((SVDBFile)p).getFilePath();
		
		fLog.debug("Opening editor for file \"" + file + "\"");
		
		// It only makes sense to set the location if the 
		// target item is not a file
		IEditorPart ed = openEditor(file);
		if (it.getType() != SVDBItemType.File) {
			if (ed instanceof SVEditor) {
				((SVEditor)ed).setSelection(it, true);
			} else if (ed instanceof SVArgFileEditor) {
				((SVArgFileEditor)ed).setSelection(it, true);
			}
		}
		
		return ed;
	}
	
	public static IEditorPart openEditor(String file) throws PartInitException {
		return openEditor(file, new String[] {SVUiPlugin.PLUGIN_ID + ".editor"});
	}
	
	public static IEditorPart openEditor(
			String 			file,
			String			restrict_editor_ids[]) throws PartInitException {
		IFile f = null;
		String name = "";
		IEditorPart ret = null;
		
		if (file != null) {
			IWorkspaceRoot root = ResourcesPlugin.getWorkspace().getRoot();

			if (file.startsWith("${workspace_loc}")) {
				file = file.substring("${workspace_loc}".length());
				f = root.getFile(new Path(file));
				
				if (f != null) {
					name = f.getFullPath().toOSString();
				}
			} else {
				f = root.getFileForLocation(new Path(file));
				if (f != null) {
					name = f.getLocation().toString();
				} else {
					name = file;
				}
			}
			
			IWorkbench wb = PlatformUI.getWorkbench();
			IWorkbenchWindow w = wb.getActiveWorkbenchWindow();

			for (IWorkbenchPage page : w.getPages()) {
				for (IEditorReference ed_r : page.getEditorReferences()) {
					String id = ed_r.getId();

					if (restrict_editor_ids != null && restrict_editor_ids.length > 0) {
						boolean found = false;
						for (String rid : restrict_editor_ids) {
							if (id.equals(rid)) {
								found = true;
								break;
							}
						}
						
						if (!found) {
							continue;
						}
					}
					
					IEditorInput in = null;

					in = ed_r.getEditorInput();
					
					if (in == null) {
						debug("Editor input is null");
					}

					if (in instanceof IURIEditorInput) {
						IURIEditorInput in_uri = (IURIEditorInput)in;
						if (in_uri.getURI() == null) {
							debug("Editor " + ed_r.getName() + " has NULL URI");
						} else {
							debug("URI path: " + in_uri.getURI().getPath());

							if (in_uri.getURI().getPath().equals(name)) {
								ret = ed_r.getEditor(true);
								break;
							}
						}
					}
				}

				if (ret != null) {
					break;
				}
			}
		}
		
		if (ret == null) {
			IWorkbenchWindow w = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
			IEditorRegistry rgy = PlatformUI.getWorkbench().getEditorRegistry();

			String leaf_name = new File(file).getName();
			IEditorDescriptor desc = rgy.getDefaultEditor(leaf_name);
			IEditorInput ed_in = null;
			
			debug("file=" + file);
			
			if (f != null) {
				ed_in = new FileEditorInput(f);
			} else if (file.startsWith("plugin:/")) {
				debug("plugin: " + file);
				IFileSystem fs = null;
				IFileStore store = null;
				try {
					fs = EFS.getFileSystem("plugin");
					store = fs.getStore(new URI(file));
				} catch (Exception e) {
					fLog.error("Failed to get plugin for " + file, e);
					e.printStackTrace();
				}

				try {
					ed_in = new PluginPathEditorInput((PluginFileStore)store);
				} catch (CoreException e) {
					fLog.error("Failed to create PluginPathEditorInput", e);
					e.printStackTrace();
				}
			} else {
				File file_path = new File(file);
				IFileStore fs = EFS.getLocalFileSystem().getStore(file_path.toURI());
				ed_in = new FileStoreEditorInput(fs);

				// TODO: need to connect up index to filesystem
			}
			
			if (desc != null) {
				ret = w.getActivePage().openEditor(ed_in, desc.getId());
			} else {
				fLog.error("Failed to find descriptor for file \"" + 
						leaf_name + "\"");
			}
		} else {
			IWorkbenchWindow w = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
			w.getActivePage().activate(ret);
		}
		
		return ret;
	}
	
	private static void debug(String msg) {
		fLog.debug(msg);
	}
}
