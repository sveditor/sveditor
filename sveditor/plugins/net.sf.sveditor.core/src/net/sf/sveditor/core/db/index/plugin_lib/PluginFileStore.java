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


package net.sf.sveditor.core.db.index.plugin_lib;

import java.io.InputStream;
import java.net.URI;
import java.net.URL;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileInfo;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.filesystem.provider.FileInfo;
import org.eclipse.core.filesystem.provider.FileStore;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

public class PluginFileStore extends FileStore {
	private URI					fURI;
	
	public PluginFileStore(URI uri) {
		fURI = uri;
	}
	
	public String getPluginPath() {
		return fURI.toString();
	}

	@Override
	public String[] childNames(int options, IProgressMonitor monitor)
			throws CoreException {
		return new String[0];
	}

	@Override
	public IFileInfo fetchInfo(int options, IProgressMonitor monitor)
			throws CoreException {
		FileInfo info = new FileInfo(getName());
		info.setExists(true);
		info.setLength(1);
		info.setDirectory(false);
		info.setAttribute(EFS.ATTRIBUTE_READ_ONLY, true);
		info.setAttribute(EFS.ATTRIBUTE_HIDDEN, false);
		
		
		return info;
	}

	@Override
	public IFileStore getChild(String name) {
		return null;
	}

	@Override
	public String getName() {
		return fURI.getPath().substring(fURI.getPath().lastIndexOf('/')+1);
	}

	@Override
	public IFileStore getParent() {
		return null;
	}

	@Override
	public InputStream openInputStream(int options, IProgressMonitor monitor)
			throws CoreException {
		
		String host = fURI.getHost();
		String path = fURI.getPath();
		
		if (host == null) {
			host = path.substring(1, path.indexOf('/', 1));
			path = path.substring(path.indexOf('/', 1)+1);
		}
		
		Bundle bundle = Platform.getBundle(host);
		URL url = bundle.getEntry(path);

		try {
			return url.openStream();
		} catch (Exception e) {
			e.printStackTrace();
			return null;
		}
	}

	@Override
	public URI toURI() {
		return fURI;
	}

}
