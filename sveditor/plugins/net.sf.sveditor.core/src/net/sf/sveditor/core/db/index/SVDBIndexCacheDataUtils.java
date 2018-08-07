package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.List;

public class SVDBIndexCacheDataUtils implements ISVDBDeclCacheFileAttr {

	/**
	 * Builds a map of what files include the specified one. 
	 * Entries are organized root->leaf (eg path)
	 * 
	 * @param ic_data
	 * @param path
	 * @return
	 */
	public static List<List<SVDBFileCacheData>> buildIncludeMap(
			SVDBIndexCacheData		ic_data,
			String					path) {
		List<List<SVDBFileCacheData>> ret = new ArrayList<List<SVDBFileCacheData>>();
		List<SVDBFileCacheData> inc_path = new ArrayList<SVDBFileCacheData>();
		
		SVDBFileCacheData cd = ic_data.getFileCacheData(path);
		
		if (cd != null) {
			inc_path.add(cd);
			buildIncludeMap(ic_data, inc_path, ret, cd);
		}

		return ret;
	}
	
	private static void buildIncludeMap(
			SVDBIndexCacheData				ic_data,
			List<SVDBFileCacheData>			inc_path,
			List<List<SVDBFileCacheData>>	ret,
			SVDBFileCacheData				cd) {
		
		// Find the thing that includes this file
		for (SVDBFileCacheData cd_i : ic_data.getFileCacheData().values()) {
			if (cd_i.getIncludedFiles().contains(cd.getFileId())) {
				// If we haven't yet processed this path
				if (!inc_path.contains(cd_i)) {
					List<SVDBFileCacheData> inc_path_i = new ArrayList<SVDBFileCacheData>(inc_path);
					inc_path_i.add(0, cd_i);
					
					if ((cd_i.getFileAttr() & FILE_ATTR_ROOT_FILE) != 0) {
						ret.add(inc_path_i);
					} else {
						// Must recurse
						buildIncludeMap(ic_data, inc_path_i, ret, cd_i);
					}
				} else {
					// TODO: I think we should just ignore this...
				}
			}
		}
	}
}
