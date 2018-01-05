package net.sf.sveditor.core.db.index.cache;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

public interface ISVDBDeclCacheInt {
	
	ISVDBDeclCache getDeclCache();

	String mapFileIdToPath(int id);
	
	SVDBFile getDeclRootFile(SVDBDeclCacheItem item);
	
	SVDBFile getDeclRootFilePP(SVDBDeclCacheItem item);
	
	List<SVDBDeclCacheItem> getScope(
			int 			rootfile_id,
			List<Integer>	scope);
}
