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
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;

import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBDeclCacheItem implements ISVDBNamedItem {
	public String						fFileName;
	
	@SVDBDoNotSaveAttr
	private ISVDBDeclCache				fParent;
	
	public String						fName;
	public SVDBItemType					fType;
	// Specifies whether this item is actually located in the FileTree view of the file.
	// This will be the case for pre-processor items
	public boolean						fIsFileTreeItem;
	
	public SVDBDeclCacheItem() {
	}
	
	public SVDBDeclCacheItem(
			ISVDBDeclCache 		parent, 
			String 				filename, 
			String 				name, 
			SVDBItemType 		type,
			boolean				is_ft_item) {
		fParent = parent;
		fFileName = filename;
		fName = name;
		fType = type;
		fIsFileTreeItem = is_ft_item;
	}
	
	public void init(ISVDBDeclCache parent) {
		fParent = parent;
	}
	
	public String getFilename() {
		return fFileName;
	}
	
	public void setFilename(String filename) {
		fFileName = filename;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public boolean isFileTreeItem() {
		return fIsFileTreeItem;
	}
	
	public void setParent(ISVDBDeclCache parent) {
		fParent = parent;
	}
	
	public ISVDBDeclCache getParent() {
		return fParent ;
	}
	
	public SVDBItemType getType() {
		return fType;
	}
	
	public void setType(SVDBItemType type) {
		fType = type;
	}
	
	public ISVDBItemBase getSVDBItem() {
		if(fParent == null) {
			// FIXME: should we also warn or generate an error here?
			return null ;
		}
		
		SVDBFile file = fParent.getDeclFile(new NullProgressMonitor(), this);
		
		if (file != null) {
			for (ISVDBChildItem c : file.getChildren()) {
				if (SVDBItem.getName(c).equals(fName) && c.getType() == getType()) {
					return c;
				} else if (c instanceof ISVDBChildParent) {
					ISVDBItemBase i = getSVDBItem((ISVDBChildParent)c);
					if (i != null) {
						return i;
					}
				} else if (getType() == SVDBItemType.TypeInfoEnumerator && 
						c.getType() == SVDBItemType.TypedefStmt) {
					SVDBTypedefStmt stmt = (SVDBTypedefStmt)c;
					if (stmt.getTypeInfo().getType() == SVDBItemType.TypeInfoEnum) {
						SVDBTypeInfoEnum e = (SVDBTypeInfoEnum)stmt.getTypeInfo();
						// Search through enumerator
						for (SVDBTypeInfoEnumerator en : e.getEnumerators()) {
							if (en.getName().equals(getName())) {
								return en;
							}
						}
					}
				}
			}
		}
		
		return null;
	}
	
	private ISVDBItemBase getSVDBItem(ISVDBChildParent p) {
		for (ISVDBChildItem c : p.getChildren()) {
			if (SVDBItem.getName(c).equals(fName) && c.getType() == fType) {
				return c;
			}
		}
		return null;
	}

	public SVDBFile getFile() {
		if (fParent == null) {
			System.out.println("Parent of " + fType + " " + fName + " is null");
			return null ;
		} else {
			return fParent.getDeclFile(new NullProgressMonitor(), this);
		}
	}
	
}

