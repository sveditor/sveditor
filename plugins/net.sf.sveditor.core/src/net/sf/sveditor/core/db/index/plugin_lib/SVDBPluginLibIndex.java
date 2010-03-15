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


package net.sf.sveditor.core.db.index.plugin_lib;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBFileSystemChangeListener;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.SVDBLibIndex;
import net.sf.sveditor.core.log.LogFactory;

import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;
import org.osgi.framework.Version;

public class SVDBPluginLibIndex extends SVDBLibIndex implements ISVDBFileSystemProvider {
	private Bundle					fBundle;
	private String					fPluginNS;
	private String					fRootFile;
	private long					fBundleVersion = -1;
	
	public SVDBPluginLibIndex(
			String 			project, 
			String 			base_location) {
		super(project, base_location, null);
		
		fLog = LogFactory.getLogHandle("SVDBPluginLibIndex");
		
		fFileSystemProvider = this;
		
		base_location = base_location.substring("plugin:/".length());
		
		fPluginNS = base_location.substring(0, base_location.indexOf('/'));
		base_location = base_location.substring(base_location.indexOf('/')+1);
		fRootFile = base_location.substring(base_location.indexOf('/')-1);
		fBundle = Platform.getBundle(fPluginNS);
		
		fLog.debug("RootFile: " + fRootFile + " Root: " + fRoot);
		
		fPreProcFileMap = new HashMap<String, SVDBFile>();
		fIndexFileMap = new HashMap<String, SVDBFile>();
	}
	
	public SVDBPluginLibIndex(
			String 			project, 
			String			plugin_ns,
			String			root) {
		super(project, "plugin:/" + plugin_ns + "/" + root, null);

		fLog = LogFactory.getLogHandle("SVDBPluginLibIndex");

		fFileSystemProvider = this;

		fRootFile = root;
		fPluginNS = plugin_ns;
		
		if (!root.startsWith("/")) {
			root = "/" + root;
		}
		fBundle = Platform.getBundle(fPluginNS);
		
		
		
		fPreProcFileMap = new HashMap<String, SVDBFile>();
		fIndexFileMap = new HashMap<String, SVDBFile>();
	}
	
	public String getTypeID() {
		return SVDBPluginLibIndexFactory.TYPE;
	}
	
	@SuppressWarnings("unchecked")
	protected List<String> getFileList() {
		String root_dir = SVFileUtils.getPathParent(fRootFile);
		List<String> ret = new ArrayList<String>();
		
		Enumeration<URL> entries = 
			(Enumeration<URL>)fBundle.findEntries(root_dir, "*", true);
		
		if (entries == null) {
			fLog.error("Failed to find bundle entry \"" + root_dir + "\"");
		}
		
		while (entries.hasMoreElements()) {
			URL url = entries.nextElement();
			
			if (url.getFile().endsWith("/")) {
				continue;
			}
			
			String ext = "";
			String path = url.getFile(); 
			if (path.lastIndexOf('.') != -1) {
				ext = path.substring(path.lastIndexOf('.'));
			}
			
			if (!fSVExtensions.contains(ext)) {
				continue;
			}

			boolean ignore = false;
			for (String ignore_dir : fIgnoreDirs) {
				if (path.contains(ignore_dir)) {
					ignore = true;
					break;
				}
			}
			
			if (ignore) {
				continue;
			}

			String full_path = "plugin:/" + fPluginNS + path;
			
			ret.add(full_path);
		}
		
		return ret;
	}
	
	public void addMarker(String path, String type, int lineno, String msg) {}

	public void clearMarkers(String path) {}

	public void closeStream(InputStream in) {
		try {
			in.close();
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
	
	public String resolvePath(String path) {
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
	
	public void addFileSystemChangeListener(ISVDBFileSystemChangeListener l) {}
	public void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l) {}


	public void rebuildIndex() {}

	public void removeChangeListener(ISVDBIndexChangeListener l) {}

	public void addChangeListener(ISVDBIndexChangeListener l) {}

	public void dispose() {}
	
}
