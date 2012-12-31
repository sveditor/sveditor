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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;

public class SVDBFileTree {
	@SVDBDoNotSaveAttr
	private boolean					fProcessed;
	
	public String					fFilePath;
	
	// Handle to the pre-processed view of the file.
	// Unused in the ArgFile context
	public SVDBFile					fSVDBFile;
	
	// List of files included in this file
	public List<String>				fIncludedFiles;
	
	// List of files in which this file is included
	public List<String>				fIncludedByFiles;

	public SVDBFileTree() {
		fFilePath = null;
		fSVDBFile = null;
		fIncludedFiles = new ArrayList<String>();
		fIncludedByFiles = new ArrayList<String>();
	}

	public SVDBFileTree(String path) {
		fFilePath = path;
		fSVDBFile = null;

		fIncludedFiles = new ArrayList<String>();
		fIncludedByFiles = new ArrayList<String>();
	}

	public SVDBFileTree(SVDBFile file) {
		fFilePath = file.getFilePath();
		
		fSVDBFile = file;
		fIncludedFiles = new ArrayList<String>();
		fIncludedByFiles = new ArrayList<String>();
	}
	
	public boolean getFileProcessed() {
		return fProcessed;
	}
	
	public void setFileProcessed(boolean is_processed) {
		fProcessed = is_processed;
	}
	
	public String getFilePath() {
		return fFilePath;
	}
	
	public void setFileName(String path) {
		fFilePath = path;
	}
	
	public SVDBFile getSVDBFile() {
		return fSVDBFile;
	}
	
	public void setSVDBFile(SVDBFile file) {
		fSVDBFile = file;
	}
	
	public List<String> getIncludedFiles() {
		return fIncludedFiles;
	}
	
	public void addIncludedFile(String path) {
		if (!fIncludedFiles.contains(path)) {
			fIncludedFiles.add(path);
		}
	}
	
	public List<String> getIncludedByFiles() {
		return fIncludedByFiles;
	}
	
	public void addIncludedByFile(String path) {
		if (!fIncludedByFiles.contains(path)) {
			fIncludedByFiles.add(path);
		}
	}

	public boolean equals(Object other) {
		if (other != null && other instanceof SVDBFileTree) {
			SVDBFileTree other_t = (SVDBFileTree)other;
			boolean ret = true;
			
			if (other_t.fFilePath == null || fFilePath == null) {
				ret &= (other_t.fFilePath == fFilePath);
			} else {
				ret &= (other_t.fFilePath.equals(fFilePath));
			}
			
			return ret;
		} else {
			return false;
		}
	}
	
	public SVDBFileTree duplicate() {
		SVDBFileTree ret = new SVDBFileTree(fFilePath);
		ret.fSVDBFile = fSVDBFile;
		ret.fIncludedByFiles.addAll(fIncludedByFiles);
		ret.fIncludedFiles.addAll(fIncludedFiles);
		
		return ret;
	}

}
