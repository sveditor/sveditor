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

import java.io.InputStream;

public interface ISVDBFileSystemProvider {
	
	String				MARKER_TYPE_ERROR   = "ERROR";
	String				MARKER_TYPE_WARNING = "WARNING";
	String				MARKER_TYPE_INFO    = "INFO";
	
	void init(String root);
	
	void dispose();
	
	void addMarker(
			String 			path,
			String			type,
			int				lineno,
			String			msg);
			
	void clearMarkers(String path);
	
	/**
	 * Resolve any relative references
	 * 
	 * @param path
	 * @return
	 */
	String resolvePath(String path);
	
	boolean fileExists(String path);
	
	InputStream openStream(String path);
	
	void closeStream(InputStream in);
	
	long getLastModifiedTime(String path);
	
	void addFileSystemChangeListener(ISVDBFileSystemChangeListener l);
	
	void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l);

}
