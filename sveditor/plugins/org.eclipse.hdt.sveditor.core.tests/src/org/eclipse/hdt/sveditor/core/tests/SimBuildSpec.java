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
package net.sf.sveditor.core.tests;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;

public class SimBuildSpec {
	
	private List<String>			fFileList;
	private List<String>			fIncDirList;
	private List<String>			fCCFlags;
	private List<String>			fCCFiles;
	
	public SimBuildSpec() {
		fFileList = new ArrayList<String>();
		fIncDirList = new ArrayList<String>();
		fCCFlags = new ArrayList<String>();
		fCCFiles = new ArrayList<String>();
	}
	
	public List<String> getFileList() {
		return fFileList;
	}
	
	public List<String> getIncDirList() {
		return fIncDirList;
	}
	
	public void addIncDir(String inc) {
		fIncDirList.add(inc);
	}

	public void addFile(String path) {
		fFileList.add(path);
	}
	
	public void addFile(IFile path) {
		fFileList.add(path.getLocation().toOSString());
	}

	public void addCCFile(String path) {
		fCCFiles.add(path);
	}
	
	public List<String> getCCFiles() {
		return fCCFiles;
	}
	
	public void addCCFlag(String flag) {
		fCCFlags.add(flag);
	}
	
	public List<String> getCCFlags() {
		return fCCFlags;
	}
}
