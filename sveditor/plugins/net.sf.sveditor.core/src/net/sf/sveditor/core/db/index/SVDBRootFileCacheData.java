package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Contains index data for a given root file
 * 
 * @author ballance
 *
 */
public class SVDBRootFileCacheData {
	public long								fLastParseTimestamp;
	public String							fPath;
	public List<String>						fIncludedFiles;
	public List<String>						fMissingIncludeFiles;
	// Declarations that might be visible without
	// a leading qualifier (eg packages, classes, tasks/functions, etc)
	public Map<String,SVDBDeclCacheItem>	fTopLevelDeclarations;
	
	// Set of identifiers referenced within this root file
	public Set<String>						fRefCache;

	public SVDBRootFileCacheData() {
		fIncludedFiles = new ArrayList<String>();
		fMissingIncludeFiles = new ArrayList<String>();
		fTopLevelDeclarations = new HashMap<String, SVDBDeclCacheItem>();
		fRefCache = new HashSet<String>();
	}
}
