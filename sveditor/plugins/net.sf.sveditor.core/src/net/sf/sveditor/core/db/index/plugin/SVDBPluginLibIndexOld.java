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


package net.sf.sveditor.core.db.index.plugin;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBFileSystemChangeListener;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.old.SVDBLibIndex;
import net.sf.sveditor.core.log.LogFactory;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;
import org.osgi.framework.Version;

public class SVDBPluginLibIndexOld extends SVDBLibIndex implements ISVDBFileSystemProvider {
	private Bundle					fBundle;
	private String					fPluginNS;
	private String					fRootFile;
	private long					fBundleVersion = -1;
	
	/*
	public SVDBPluginLibIndex(
			String 			project, 
			String 			base_location,
			ISVDBIndexCache	cache) {
		super(project, base_location, null, cache, null);
		
		fLog = LogFactory.getLogHandle("SVDBPluginLibIndex");
		
		setFileSystemProvider(this);
		
		base_location = base_location.substring("plugin:/".length());
		
		fPluginNS = base_location.substring(0, base_location.indexOf('/'));
		base_location = base_location.substring(base_location.indexOf('/')+1);
		fRootFile = base_location.substring(base_location.indexOf('/')-1);
		fBundle = Platform.getBundle(fPluginNS);
		
		fLog.debug("RootFile: " + fRootFile + " Root: " + getBaseLocation());
	}
	 */
	
	public SVDBPluginLibIndexOld(
			String 			project, 
			String			index_id,
			String			plugin_ns,
			String			root,
			ISVDBIndexCache	cache) {
//		super(project, "plugin:/" + plugin_ns + "/" + root, null, cache, null);
		super(project, index_id, null, cache, null);

		fLog = LogFactory.getLogHandle("SVDBPluginLibIndex");
		fRootFile = root;
		fPluginNS = plugin_ns;
		
		fBundle = Platform.getBundle(fPluginNS);
		fLog.debug("RootFile: " + fRootFile + " Root: " + getBaseLocation());
		setFileSystemProvider(this);
	}
	
	@Override
	public String getResolvedBaseLocation() {
		return "plugin:/" + fPluginNS + "/" + fRootFile;
	}



	public String getTypeID() {
		return SVDBPluginLibIndexFactory.TYPE;
	}
	
	@Override
	protected void discoverRootFiles(IProgressMonitor monitor) {
		clearFilesList();
		clearIncludePaths();
		addFile(getResolvedBaseLocation(), false);
		addIncludePath(getResolvedBaseLocationDir());
	}

	public boolean isDir(String path) {
 		if (path.startsWith("plugin:/")) {
 			URL entry;

			String leaf = path.substring(("plugin:/" + fPluginNS).length());

			return ((entry = fBundle.getEntry(leaf)) != null && entry.getPath().endsWith("/"));
		} else {
			return false;
		}
	}
	
	public List<String> getFiles(String path) {
		// TODO: Don't support this currently for plugin library
		return new ArrayList<String>();
	}

	public void addMarker(String path, String type, int lineno, String msg) {}

	public void clearMarkers(String path) {}

	public void closeStream(InputStream in) {
		try {
			in.close();
		} catch (IOException e) {}
	}
	
	public void closeStream(OutputStream out) {
		try {
			out.close();
		} catch (IOException e) {}
	}

	public boolean fileExists(String path) {
 		if (path.startsWith("plugin:/")) {

			String leaf = path.substring(("plugin:/" + fPluginNS).length());

			return (fBundle.getEntry(leaf) != null);
		} else {
			return false;
		}
	}
	
	public String resolvePath(String path, String fmt) {
		return path;
	}

	// Init for ISVDBFileSystem interface
	public void init(String root) {}

	public InputStream openStream(String path) {
		InputStream ret = null;
		
		if (path.startsWith("plugin:/")) {

			String leaf = path.substring(("plugin:/" + fPluginNS).length());

			URL url = fBundle.getEntry(leaf);

			if (url != null) {
				try {
					ret = url.openStream();
				} catch (IOException e) {
					fLog.error("Failed to open plugin file \"" + 
							path + "\"", e);
				}
			}
		}
		
		return ret;
	}
	
	public OutputStream openStreamWrite(String path) {
		return null;
	}
	
	public long getLastModifiedTime(String file) {
		if (fBundleVersion == -1) {
			Version v = SVCorePlugin.getDefault().getBundle().getVersion();
			// Ensure the version is always really big to work around the temporary 
			// current problem of having existing versions out in the wild
			fBundleVersion  = v.getMicro();
			fBundleVersion |= v.getMinor() << 16;
			fBundleVersion |= v.getMajor() << 24;
			fBundleVersion |= (8L << 48L);
		}
		if (fBundleVersion < fBundle.getLastModified()) {
			System.out.println("computed bundle version older than BundleVersion: " +
					fBundleVersion + " " + fBundle.getLastModified());
		}
		
		return fBundleVersion;
	}

	@Override
	public void dispose() {
		if (getCache() != null) {
			getCache().sync();
		}
	}

	public void addFileSystemChangeListener(ISVDBFileSystemChangeListener l) {}
	public void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l) {}

}
