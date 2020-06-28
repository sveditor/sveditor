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


package org.eclipse.hdt.sveditor.core.db.index;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.List;

public class SVDBFSFileSystemProvider implements ISVDBFileSystemProvider {
	
	public void init(String path) {}
	
	public void dispose() {}
	
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
		File f = new File(path);
		return f.isFile();
	}
	
	public boolean isDir(String path) {
		File f = new File(path);
		return f.isDirectory();
	}
	
	public List<String> getFiles(String path) {
		File p = new File(path);
		List<String> ret = new ArrayList<String>();
		
		if (p.isDirectory()) {
			File f_l[] = p.listFiles();
			if (f_l != null) {
				for (File f : p.listFiles()) {
					if (!f.getName().equals(".") && !f.getName().equals("..")) {
						ret.add(f.getAbsolutePath().replace('\\', '/'));
					}
				}
			}
		}
		
		return ret;
	}

	public long getLastModifiedTime(String path) {
		File f = new File(path);
		
		return f.lastModified();
	}
	
	public String resolvePath(String path, String fmt) {
		return path;
	}

	public InputStream openStream(String path) {
		InputStream in = null;
		
		try {
			in = new FileInputStream(path);
		} catch (IOException e) { }
		
		return in;
	}

	public OutputStream openStreamWrite(String path) {
		OutputStream out = null;
		
		try {
			out = new FileOutputStream(path);
		} catch (IOException e) { }
		
		return out;
	}
	
	public void addFileSystemChangeListener(ISVDBFileSystemChangeListener l) {
		// TODO Auto-generated method stub
		
	}

	public void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l) {
		// TODO Auto-generated method stub
		
	}
	
}
