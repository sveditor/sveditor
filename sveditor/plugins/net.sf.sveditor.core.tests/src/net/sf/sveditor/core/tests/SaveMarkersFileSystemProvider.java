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


package net.sf.sveditor.core.tests;

import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.db.index.ISVDBFileSystemChangeListener;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;

public class SaveMarkersFileSystemProvider implements ISVDBFileSystemProvider {
	private ISVDBFileSystemProvider			fFSProvider;
	private Map<String, List<String>>		fMarkersMap;
	
	public SaveMarkersFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		fFSProvider = fs_provider;
		fMarkersMap = new HashMap<String, List<String>>();
	}
	
	public List<String> getMarkers() {
		List<String> ret = new ArrayList<String>();
		
		for (Entry<String, List<String>> e : fMarkersMap.entrySet()) {
			ret.addAll(e.getValue());
		}
		
		return ret;
	}

	public void addFileSystemChangeListener(ISVDBFileSystemChangeListener l) {
		fFSProvider.addFileSystemChangeListener(l);
	}

	public synchronized void addMarker(String path, String type, int lineno, String msg) {
		if (!fMarkersMap.containsKey(path)) {
			fMarkersMap.put(path, new ArrayList<String>());
		}
		fMarkersMap.get(path).add(msg);

		fFSProvider.addMarker(path, type, lineno, msg);
	}
	

	public void clearMarkers(String path) {
		fFSProvider.clearMarkers(path);
		if (fMarkersMap.containsKey(path)) {
			fMarkersMap.get(path).clear();
		}
	}

	public void closeStream(InputStream in) {
		fFSProvider.closeStream(in);
	}
	
	public void closeStream(OutputStream out) {
		fFSProvider.closeStream(out);
	}

	public void dispose() {
		fFSProvider.dispose();
	}

	public boolean fileExists(String path) {
		return fFSProvider.fileExists(path);
	}

	public boolean isDir(String path) {
		return fFSProvider.isDir(path);
	}
	
	public List<String> getFiles(String path) {
		return fFSProvider.getFiles(path);
	}

	public long getLastModifiedTime(String path) {
		return fFSProvider.getLastModifiedTime(path);
	}

	public void init(String root) {
		fFSProvider.init(root);
	}

	public InputStream openStream(String path) {
		return fFSProvider.openStream(path);
	}
	
	public OutputStream openStreamWrite(String path) {
		return fFSProvider.openStreamWrite(path);
	}

	public void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l) {
		fFSProvider.removeFileSystemChangeListener(l);
	}

	public String resolvePath(String path, String fmt) {
		return fFSProvider.resolvePath(path, fmt);
	}

}
