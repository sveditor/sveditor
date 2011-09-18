/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;

import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBDeclCacheItem implements ISVDBNamedItem {
	@SVDBDoNotSaveAttr
	private String						fFileName;
	
	@SVDBDoNotSaveAttr
	private ISVDBDeclCache				fParent;
	
	private String						fName;
	private SVDBItemType				fType;
	
	public SVDBDeclCacheItem() {
	}
	
	public SVDBDeclCacheItem(ISVDBDeclCache parent, String filename, String name, SVDBItemType type) {
		fParent = parent;
		fFileName = filename;
		fName = name;
		fType = type;
	}
	
	public void init(String filename, ISVDBDeclCache parent) {
		fFileName = filename;
		fParent = parent;
	}
	
	public String getFilename() {
		return fFileName;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public SVDBItemType getType() {
		return fType;
	}
	
	public void setType(SVDBItemType type) {
		fType = type;
	}
	
	public ISVDBItemBase getSVDBItem() {
		SVDBFile file = fParent.getDeclFile(new NullProgressMonitor(), this);
		
		if (file != null) {
			for (ISVDBChildItem c : file.getChildren()) {
				if (SVDBItem.getName(c).equals(fName) && c.getType() == getType()) {
					return c;
				}
			}
		}
		
		return null;
	}

	public SVDBFile getFile() {
		return fParent.getDeclFile(new NullProgressMonitor(), this);
	}
	
}

