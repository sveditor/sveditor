package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sf.sveditor.core.db.SVDBLang;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;

/**
 * Contains index data for a given root file
 * 
 * @author ballance
 *
 */
public class SVDBFileCacheData {
	public long								fLastParseTimestamp;
	/*
	 * @see ISVDBDeclCache
	 */
	public int								fFileAttr;
	public int								fFileId;
	public Set<Integer>						fIncludedFiles;
	public Set<String>						fMissingIncludeFiles;
	
	// Declarations that might be visible without
	// a leading qualifier (eg packages, classes, tasks/functions, etc)
	@SVDBDoNotSaveAttr
	public List<SVDBDeclCacheItem>			fTopLevelDeclarations;
	
	// Set of identifiers referenced within this root file
	// and any included files
	public Set<String>						fRefCache;
	
	public SVDBLang							fLanguage;

	public SVDBFileCacheData() {
		fIncludedFiles = new HashSet<Integer>();
		fMissingIncludeFiles = new HashSet<String>();
		fTopLevelDeclarations = new ArrayList<SVDBDeclCacheItem>();
		fRefCache = new HashSet<String>();
	}
	
	public SVDBFileCacheData(int id, int attr) {
		this();
		fFileId = id;
		fFileAttr = attr;
	}
	
	public long getLastParseTimestamp() { return fLastParseTimestamp; }
	
	public void setLastParseTimestamp(long ts) { fLastParseTimestamp = ts; }
	
	public int getFileAttr() { return fFileAttr; }
	
	public void setFileAttr(int attr) { fFileAttr = attr; }
	
	public int getFileId() { return fFileId; }
	
	public void setFileId(int id) { fFileId = id; }
	
	public Set<String> getRefCache() { return fRefCache; }
	
	public List<SVDBDeclCacheItem> getTopLevelDeclarations() { return fTopLevelDeclarations; }
	
	public Set<Integer> getIncludedFiles() { return fIncludedFiles; }
	
	public Set<String> getMissingIncludeFiles() { return fMissingIncludeFiles; }
	
	public void addIncludedFile(int id) {
		fIncludedFiles.add(id);
	}

	public boolean findChildrenOf(
			List<SVDBDeclCacheItem>		children,
			SVDBDeclCacheItem			item) {
		int item_idx = fTopLevelDeclarations.indexOf(item);
		boolean ret = false;
		
		if (item_idx != -1) {
			// Iterate through looking for items where this is listed
			for (SVDBDeclCacheItem i : fTopLevelDeclarations) {
				if (i.getScopeIDs().contains(item_idx)) {
					children.add(i);
					ret = true;
				}
			}
		}
		
		return ret;
	}
}
