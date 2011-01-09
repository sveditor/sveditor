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


package net.sf.sveditor.ui;

import java.io.File;
import java.net.URI;

import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.plugin_lib.PluginFileStore;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.ui.editor.SVEditor;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.filesystem.IFileSystem;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
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
	
	public static IEditorPart openEditor(SVDBItem it) throws PartInitException {
		ISVDBNamedItem p = it;
		// Find the file that this item belongs to
		
		while (p != null && p.getType() != SVDBItemType.File) {
			p = p.getParent();
		}
		
		String file = ((SVDBFile)p).getFilePath();
		
		IEditorPart ed = openEditor(file);
		if (ed instanceof SVEditor) {
			((SVEditor)ed).setSelection(it, true);
		}
		
		return ed;
	}
	
	public static IEditorPart openEditor(String file) throws PartInitException {
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

					if (!id.equals(SVUiPlugin.PLUGIN_ID + ".editor")) {
						continue;
					}
					IEditorInput in = null;

					in = ed_r.getEditorInput();

					if (in instanceof IURIEditorInput) {
						IURIEditorInput in_uri = (IURIEditorInput)in;

						debug("URI path: " + in_uri.getURI().getPath());
						
						if (in_uri.getURI().getPath().equals(name)) {
							ret = ed_r.getEditor(true);
							break;
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
			ret = w.getActivePage().openEditor(ed_in, desc.getId());
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
