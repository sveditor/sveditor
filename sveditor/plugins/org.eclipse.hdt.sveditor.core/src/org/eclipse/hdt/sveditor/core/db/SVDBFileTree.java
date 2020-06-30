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


package org.eclipse.hdt.sveditor.core.db;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.hdt.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import org.eclipse.hdt.sveditor.core.db.attr.SVDBParentAttr;

public class SVDBFileTree extends SVDBItemBase implements ISVDBChildItem {
	@SVDBDoNotSaveAttr
	private boolean						fProcessed;
	
	@SVDBParentAttr
	public ISVDBChildItem				fParent;

	// 
	public String						fFilePath;

	// Specifies whether this file defines a new
	// root scope. This flag is used by 
	// argument files. An argument file included
	// with -F will have this flag set. An
	// argument file included with -f will have 
	// this flag cleared
	public boolean						fIncludeRoot;
	
	// Handle to the pre-processed view of the file.
	public SVDBFile						fSVDBFile;
	
	// List of markers for the pre-processor view
	public List<SVDBMarker>				fMarkers;
	
	// List of files included in this file
	public List<String>					fIncludedFiles;
	
	/**
	 * List of incoming macros to this root file when
	 * in MFCU mode. This field is not used in SFCU mode.
	 */
	public List<SVDBMacroDef>			fMFCUIncomingMacros;
	
	// List of macro sets defined by this file prior to
	// each included file. Element '0' contains the 
	// macros defined in this file prior to the inclusion
	// of IncludedFileTrees[0]
	public List<SVDBFileTreeMacroList>	fMacroSetList;

	// List of file trees corresponding to files included by
	// this one. Used by the 'new' index flow 
	public List<SVDBFileTree>			fIncludedFileTrees;
	
	// List of files in which this file is included
	public List<String>					fIncludedByFiles;
	
	// List of macros (and their defined values) referenced in this file
	public Map<String, String>			fReferencedMacros;

	public SVDBFileTree() {
		super(SVDBItemType.FileTree);
		fFilePath = null;
		fSVDBFile = null;
		fIncludedFiles = new ArrayList<String>();
		fIncludedByFiles = new ArrayList<String>();
		fMacroSetList = new ArrayList<SVDBFileTreeMacroList>();
		fMacroSetList.add(new SVDBFileTreeMacroList());
		fIncludedFileTrees = new ArrayList<SVDBFileTree>();
		fReferencedMacros = new HashMap<String, String>();
		fMarkers = new ArrayList<SVDBMarker>();
	}

	public SVDBFileTree(String path) {
		super(SVDBItemType.FileTree);
		fFilePath = path;
		fSVDBFile = null;

		fIncludedFiles = new ArrayList<String>();
		fIncludedByFiles = new ArrayList<String>();
		fMacroSetList = new ArrayList<SVDBFileTreeMacroList>();
		fMacroSetList.add(new SVDBFileTreeMacroList());
		fIncludedFileTrees = new ArrayList<SVDBFileTree>();
		fReferencedMacros = new HashMap<String, String>();
		fMarkers = new ArrayList<SVDBMarker>();
	}

	public SVDBFileTree(SVDBFile file) {
		super(SVDBItemType.FileTree);
		fFilePath = file.getFilePath();
		
		fSVDBFile = file;
		fIncludedFiles = new ArrayList<String>();
		fMacroSetList = new ArrayList<SVDBFileTreeMacroList>();
		fMacroSetList.add(new SVDBFileTreeMacroList());
		fIncludedByFiles = new ArrayList<String>();
		fIncludedFileTrees = new ArrayList<SVDBFileTree>();
		fReferencedMacros = new HashMap<String, String>();
		fMarkers = new ArrayList<SVDBMarker>();
	}
	
	public void setParent(SVDBFileTree parent) {
		fParent = parent;
	}
	
	public SVDBFileTree getParent() {
		return (SVDBFileTree)fParent;
	}
	
	public void setParent(ISVDBChildItem parent) {
		fParent = parent;
	}

	public boolean isIncludeRoot() {
		return fIncludeRoot;
	}
	
	public void setIncludeRoot(boolean root) {
		fIncludeRoot = root;
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
	
	public List<SVDBMarker> getMarkers() {
		return fMarkers;
	}
	
	public void addIncludedFileTree(SVDBFileTree ft) {
		fIncludedFileTrees.add(ft);
		fMacroSetList.add(new SVDBFileTreeMacroList());
	}
	
	public List<SVDBFileTree> getIncludedFileTreeList() {
		return fIncludedFileTrees;
	}
	
	public void addToMacroSet(SVDBMacroDef m) {
		SVDBFileTreeMacroList ml = fMacroSetList.get(fMacroSetList.size()-1);
		ml.addMacro(m);
	}
	
	public List<SVDBFileTreeMacroList> getMacroSetList() {
		return fMacroSetList;
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
