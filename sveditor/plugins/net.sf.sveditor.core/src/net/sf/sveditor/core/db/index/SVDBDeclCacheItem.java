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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLang;
import net.sf.sveditor.core.db.SVDBTypeInfoEnum;
import net.sf.sveditor.core.db.SVDBTypeInfoEnumerator;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.index.cache.ISVDBDeclCacheInt;
import net.sf.sveditor.core.db.stmt.SVDBImportItem;
import net.sf.sveditor.core.db.stmt.SVDBImportStmt;
import net.sf.sveditor.core.db.stmt.SVDBTypedefStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBDeclCacheItem implements ISVDBNamedItem {
	
	// TODO: should change this to a file id
	// TODO: Old Index
	public String						fFileName;

	// New Index
	public int							fRootFileId;
	public int							fFileId;
	
	@SVDBDoNotSaveAttr
	private ISVDBDeclCacheInt			fParent;
	@SVDBDoNotSaveAttr
	private ISVDBDeclCache				fParentOld;
	
	public String						fName;

	// TODO: Old Index (Used to store base-class list)
	public List<String>					fExtList;

	// New Index
	// List of indexes into the root-file declaration
	// cache, specifying the containing scope (if any)
	// of this type
	public List<Integer>				fScope;
	
	public SVDBItemType					fType;
	
	// Tracks the language that this item belongs to. 
	// This is import to allow content assist, for example,
	// to not provide the user SystemVerilog proposals while
	// editing a VHDL file
	public SVDBLang						fLanguage;
	
	// Specifies whether this item is actually located in the FileTree view of the file.
	// This will be the case for pre-processor items
	public boolean						fIsFileTreeItem;

	@SVDBDoNotSaveAttr
	private static LogHandle			fLog;
	
	public SVDBDeclCacheItem() {
	}

	@Deprecated
	public SVDBDeclCacheItem(
			ISVDBDeclCache 		parent, 
			String 				filename, 
			String 				name, 
			SVDBItemType 		type,
			boolean				is_ft_item) {
		fParentOld = parent;
		fFileName = filename;
		fName = name;
		fType = type;
		fIsFileTreeItem = is_ft_item;
	}

	public SVDBDeclCacheItem(
			ISVDBDeclCacheInt	parent,
			int					rootfile_id,
			int					file_id,
			List<Integer>		scope,
			String				name,
			SVDBItemType		type,
			boolean				is_ft_item) {
		fParent = parent;
		fParentOld = parent.getDeclCache();
		fRootFileId = rootfile_id;
		fFileId = file_id;
		fScope = new ArrayList<Integer>(scope);
		fName = name;
		fType = type;
		fIsFileTreeItem = is_ft_item;
	}
	
	public void init(ISVDBDeclCacheInt parent) {
		fParent = parent;
		fParentOld = parent.getDeclCache();
	}
	
	public void init(ISVDBDeclCache parent) {
		fParentOld = parent;
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
	
	public void setParent(ISVDBDeclCacheInt parent) {
		fParent = parent;
		fParentOld = parent.getDeclCache();
	}
	
	public ISVDBDeclCache getParent() {
		return fParentOld;
	}
	
	public SVDBItemType getType() {
		return fType;
	}
	
	public void setType(SVDBItemType type) {
		fType = type;
	}
	
	public ISVDBItemBase getSVDBItem() {
		ISVDBItemBase ret = null;
		
		if(fParentOld != null) {
			SVDBFile file = fParentOld.getDeclFile(new NullProgressMonitor(), this);
			
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
				fLog.debug("Error: Failed to find file=" + fFileName + " in cache " +
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
			return fParentOld.getDeclFile(new NullProgressMonitor(), this);
		}
	}
	
	public SVDBFile getFilePP() {
		if (fParent == null) {
			return null ;
		} else {
			return fParent.getDeclCache().getDeclFilePP(new NullProgressMonitor(), this);
		}
	}
}

