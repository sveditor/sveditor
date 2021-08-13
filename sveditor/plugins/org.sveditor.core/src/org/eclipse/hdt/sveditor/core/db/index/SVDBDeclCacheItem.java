/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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

import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildParent;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfoEnum;
import org.eclipse.hdt.sveditor.core.db.SVDBTypeInfoEnumerator;
import org.eclipse.hdt.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBImportItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBImportStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBTypedefStmt;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclItem;
import org.eclipse.hdt.sveditor.core.db.stmt.SVDBVarDeclStmt;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class SVDBDeclCacheItem implements ISVDBNamedItem {
	// TODO: should change this to a file id
	public String						fFileName;
	
	@SVDBDoNotSaveAttr
	private ISVDBDeclCache				fParent;
	
	public String						fName;

	// Used to store base-class list
	public List<String>					fExtList;
	
	public SVDBItemType					fType;
	
	// Specifies whether this item is actually located in the FileTree view of the file.
	// This will be the case for pre-processor items
	public boolean						fIsFileTreeItem;

	@SVDBDoNotSaveAttr
	private static LogHandle			fLog;
	
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
		ISVDBItemBase ret = null;
		
		if(fParent != null) {
			SVDBFile file = fParent.getDeclFile(new NullProgressMonitor(), this);
			
			if (file != null) {
				ret = findSVDBItem(file);
				
				if (ret == null) {
					if (fLog == null) {
						fLog = LogFactory.getLogHandle("SVDBDeclCacheItem");
					}
					Exception e = null;
					try { throw new Exception(); } catch (Exception e2) { e = e2; }
					fLog.debug("Error: Failed to find item name=" + fName + 
							" type=" + fType + " in file=" + fFileName + 
							" (isFileTreeItem=" + fIsFileTreeItem + ")", e);
				}
			} else {
				if (fLog == null) {
					fLog = LogFactory.getLogHandle("SVDBDeclCacheItem");
				}
				Exception e = null;
				try { throw new Exception(); } catch (Exception e2) { e = e2; }
				fLog.debug("Error: Failed to file=" + fFileName + " in cache " +
						"while looking for item name=" + fName + " type=" + 
						fType + " (isFileTreeItem=" + fIsFileTreeItem + ")", e);
			}
		} else {
			// FIXME: should we also warn or generate an error here?
			if (fLog == null) {
				fLog = LogFactory.getLogHandle("SVDBDeclCacheItem");
			}
			Exception e = null;
			try { throw new Exception(); } catch (Exception e2) { e = e2; }
			
			fLog.debug("Error: 'parent' is null while looking for item " +
					"name=" + fName + " type=" + fType + " in file=" + fFileName +
					" (isFileTreeItem=" + fIsFileTreeItem + ")", e);
		}
		
		return ret;
	}
	
	private ISVDBItemBase findSVDBItem(ISVDBChildParent scope) {
		for (ISVDBChildItem c : scope.getChildren()) {
			if (SVDBItem.getName(c).equals(fName) && c.getType() == getType()) {
				return c;
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
			} else if (getType() == SVDBItemType.VarDeclItem &&
					c.getType() == SVDBItemType.VarDeclStmt) {
				SVDBVarDeclStmt vs = (SVDBVarDeclStmt)c;
				for (ISVDBChildItem ci : vs.getChildren()) {
					SVDBVarDeclItem vi = (SVDBVarDeclItem)ci;
					if (vi.getName().equals(getName())) {
						return vi;
					}
				}
			} else if (c.getType() == SVDBItemType.PackageDecl) {
				ISVDBItemBase tmp = findSVDBItem((ISVDBChildParent)c);
				
				if (tmp != null) {
					return tmp;
				}
			} else if (c.getType() == SVDBItemType.ImportStmt) {
				SVDBImportStmt s = (SVDBImportStmt)c;
				for (ISVDBChildItem ci : s.getChildren()) {
					SVDBImportItem i = (SVDBImportItem)ci;
					if (i.getImport().equals(fName)) {
						return i;
					}
				}
			} else if (c instanceof ISVDBChildParent) {
				ISVDBItemBase i = getSVDBItem((ISVDBChildParent)c);
				if (i != null) {
					return i;
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
			return null ;
		} else {
			return fParent.getDeclFile(new NullProgressMonitor(), this);
		}
	}
	
	public SVDBFile getFilePP() {
		if (fParent == null) {
			return null ;
		} else {
			return fParent.getDeclFilePP(new NullProgressMonitor(), this);
		}
	}
}

