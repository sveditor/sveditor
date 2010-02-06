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


package net.sf.sveditor.core.db;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class DB {
	private List<SVDBFile>				fFiles;
	private List<SVDBItem>				fItems;
	
	
	public DB() {
		fFiles = new ArrayList<SVDBFile>();
		fItems = new ArrayList<SVDBItem>();
	}
	

	public SVDBFile findFile(File path) {
		/*
		for (SVDBFile f : fFiles) {
			if (f.getFile().equals(path)) {
				return f;
			}
		}
		 */
		return null;
	}
	
	public List<SVDBFile> getFiles() {
		return fFiles;
	}

	public void addFile(SVDBFile file) {
		fFiles.add(file);
	}
	
	public void addItem(SVDBItem it) {
		fItems.add(it);
	}
	
	public void removeFile(SVDBFile file) {
		fFiles.remove(file);
		for (SVDBItem it : file.getItems()) {
			fItems.remove(it);
		}
	}
	
	public void updateFile(SVDBFile file) {
		removeFile(file);
		addFile(file);
	}

}
