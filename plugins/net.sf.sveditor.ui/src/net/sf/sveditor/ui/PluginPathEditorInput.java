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

import java.net.URI;

import net.sf.sveditor.core.db.index.plugin_lib.PluginFileStore;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.IPersistableElement;
import org.eclipse.ui.editors.text.ILocationProvider;
import org.eclipse.ui.editors.text.ILocationProviderExtension;
import org.eclipse.ui.ide.FileStoreEditorInput;

public class PluginPathEditorInput extends FileStoreEditorInput {
	PluginFileStore				fFileStore;
	
	public PluginPathEditorInput(PluginFileStore file) throws CoreException {
		super(file);
		
		fFileStore = file;
	}
	
	public PluginFileStore getFileStore() {
		return fFileStore;
	}

	public IPersistableElement getPersistable() {
		return this;
	}

	@SuppressWarnings("unchecked")
	public Object getAdapter(Class adapter) {
		if (IFile.class.equals(adapter) || IResource.class.equals(adapter)) {
			return null;
		} else if (ILocationProvider.class.equals(adapter)) {
			return new LocationProvider((PluginFileStore)fFileStore);
		} else {
			return super.getAdapter(adapter);
		}
	}
	
	public boolean equals(Object o) {
		if (o == this) {
			return true;
		}
		
		if (o instanceof PluginPathEditorInput) {
			PluginPathEditorInput in = (PluginPathEditorInput)o;
			return fFileStore.equals(in.fFileStore);
		}
		
		return false;
	}
	
	public String getFactoryId() {
		return PluginFileEditorInputFactory.ID;
	}

	public void saveState(IMemento memento) {
		PluginFileEditorInputFactory.saveState(memento, this);
	}

	private class LocationProvider implements ILocationProvider, ILocationProviderExtension {
		PluginFileStore 		fFileStore;
		
		public LocationProvider(PluginFileStore fs) {
			fFileStore = fs;
		}

		public URI getURI(Object element) {
			String path = ((PluginFileStore)fFileStore).getPluginPath();
			try {
				return new URI(path);
			} catch (Exception e) {
				e.printStackTrace();
			}
			return null;
		}

		public IPath getPath(Object element) {
			String path = ((PluginFileStore)fFileStore).getPluginPath();
			
			return new Path(path);
		}
	};

}
