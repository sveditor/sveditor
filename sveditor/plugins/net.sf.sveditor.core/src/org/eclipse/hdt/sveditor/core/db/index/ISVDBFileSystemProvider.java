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
