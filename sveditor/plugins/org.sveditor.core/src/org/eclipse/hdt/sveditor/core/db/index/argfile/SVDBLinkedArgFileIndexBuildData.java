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
import org.eclipse.core.runtime.SubMonitor;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBFileTree;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;

public class SVDBLinkedArgFileIndexBuildData implements
		ISVDBArgFileIndexBuildData {
	private ISVDBArgFileIndexBuildData			fBacking;
	private ISVDBArgFileIndexBuildData			fPrimary;
	
	public SVDBLinkedArgFileIndexBuildData(
			ISVDBArgFileIndexBuildData		primary,
			ISVDBArgFileIndexBuildData		backing) {
		fBacking = backing;
		fPrimary = primary;
	}

	@Override
	public void addFile(String path, boolean is_argfile) {
		fPrimary.addFile(path, is_argfile);
	}

	@Override
	public void removeFile(String path, boolean is_argfile) {
		fPrimary.removeFile(path, is_argfile);
	}

	@Override
	public SVDBFile getFile(IProgressMonitor monitor, String path) {
		SVDBFile ret;
		SubMonitor subMonitor = SubMonitor.convert(monitor, 2);
		
		if ((ret = fPrimary.getFile(subMonitor.newChild(1), path)) == null) {
			ret = fBacking.getFile(subMonitor.newChild(1), path);
		}
		else  {
			subMonitor.done();
		}
		
		return ret;
	}

	@Override
	public void setFile(String path, SVDBFile file, boolean is_argfile) {
		fPrimary.setFile(path, file, is_argfile);
	}

	@Override
	public void setLastModified(String path, long timestamp, boolean is_argfile) {
		fPrimary.setLastModified(path, timestamp, is_argfile);
	}

	@Override
	public void setMarkers(
			String 				path, 
			List<SVDBMarker> 	markers,
			boolean 			is_argfile) {
		fPrimary.setMarkers(path, markers, is_argfile);
	}

	@Override
	public List<SVDBMarker> getMarkers(String path) {
		return fPrimary.getMarkers(path);
	}

	@Override
	public void setFileTree(String path, SVDBFileTree file, boolean is_argfile) {
		fPrimary.setFileTree(path, file, is_argfile);
	}

	@Override
	public void addIncludePath(String path) {
		fPrimary.addIncludePath(path);
	}

	@Override
	public void addArgFilePath(String path) {
		fPrimary.addArgFilePath(path);
	}

	@Override
	public void addArgFile(SVDBFile argfile) {
		fPrimary.addArgFile(argfile);
	}

	@Override
	public void addDefine(String key, String val) {
		fPrimary.addDefine(key, val);
	}

	@Override
	public void setMFCU() {
		fPrimary.setMFCU();
	}

	@Override
	public boolean isMFCU() {
		return fPrimary.isMFCU();
	}

	@Override
	public void setForceSV(boolean force) {
		fPrimary.setForceSV(force);
	}

	@Override
	public boolean getForceSV() {
		return fPrimary.getForceSV();
	}

	@Override
	public void addLibFile(String path) {
		fPrimary.addLibFile(path);
	}

}
