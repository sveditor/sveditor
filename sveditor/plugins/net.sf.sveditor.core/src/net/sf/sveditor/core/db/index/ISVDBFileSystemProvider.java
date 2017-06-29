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


package net.sf.sveditor.core.db.index;

import java.io.InputStream;
import java.io.OutputStream;
import java.util.List;

public interface ISVDBFileSystemProvider extends ISVDBMarkerMgr {
	
	String				PATHFMT_FILESYSTEM = "PATHFMT_FS";
	String				PATHFMT_WORKSPACE  = "PATHFMT_WS";
	
	void init(String root);
	
	void dispose();

	
	/**
	 * Resolve any relative references
	 * 
	 * @param path
	 * @param fmt - 
	 * @return
	 */
	String resolvePath(String path, String fmt);
	
	boolean fileExists(String path);
	
	boolean isDir(String path);
	
	List<String> getFiles(String path);
	
	InputStream openStream(String path);
	
	OutputStream openStreamWrite(String path);
	
	void closeStream(InputStream in);
	
	void closeStream(OutputStream in);
	
	long getLastModifiedTime(String path);
	
	void addFileSystemChangeListener(ISVDBFileSystemChangeListener l);
	
	void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l);

}
