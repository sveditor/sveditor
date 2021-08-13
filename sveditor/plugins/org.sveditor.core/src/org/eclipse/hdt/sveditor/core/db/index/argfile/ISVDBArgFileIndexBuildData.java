/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.core.db.index.argfile;

import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBFileTree;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;

public interface ISVDBArgFileIndexBuildData {
	
	void addFile(String path, boolean is_argfile);
	
	void removeFile(String path, boolean is_argfile);
	
	SVDBFile getFile(IProgressMonitor monitor, String path);

	void setFile(String path, SVDBFile file, boolean is_argfile);
	void setLastModified(String path, long timestamp, boolean is_argfile);
	void setMarkers(String path, List<SVDBMarker> markers, boolean is_argfile);
	List<SVDBMarker> getMarkers(String path);
	void setFileTree(String path, SVDBFileTree file, boolean is_argfile);
	
	void addIncludePath(String path);
	
	void addArgFilePath(String path);
	
	void addArgFile(SVDBFile argfile);
	
	void addDefine(String key, String val);
	
	void setMFCU();
	
	boolean isMFCU();

	void setForceSV(boolean force);
	
	boolean getForceSV();
	
	void addLibFile(String path);
	
}
