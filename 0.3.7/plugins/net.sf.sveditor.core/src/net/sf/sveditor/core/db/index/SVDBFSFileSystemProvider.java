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


package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

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

	public boolean fileExists(String path) {
		File f = new File(path);
		return f.isFile();
	}

	public long getLastModifiedTime(String path) {
		File f = new File(path);
		
		return f.lastModified();
	}
	
	public String resolvePath(String path) {
		return path;
	}

	public InputStream openStream(String path) {
		InputStream in = null;
		
		try {
			InputStream t_in = new FileInputStream(path);
			// in = new BufferedInputStream(t_in, 4*1024);
			in = t_in;
		} catch (IOException e) { }
		
		return in;
	}

	public void addFileSystemChangeListener(ISVDBFileSystemChangeListener l) {
		// TODO Auto-generated method stub
		
	}

	public void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l) {
		// TODO Auto-generated method stub
		
	}
	
}
