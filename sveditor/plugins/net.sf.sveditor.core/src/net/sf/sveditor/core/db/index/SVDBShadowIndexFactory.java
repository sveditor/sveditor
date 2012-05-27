package net.sf.sveditor.core.db.index;

import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.project.SVDBSourceCollection;
import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;
import net.sf.sveditor.core.fileset.SVFileSet;
import net.sf.sveditor.core.fileset.SVFilesystemFileMatcher;
import net.sf.sveditor.core.fileset.SVWorkspaceFileMatcher;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBShadowIndexFactory implements ISVDBIndexFactory {
	public static final String	TYPE = "net.sf.sveditor.shadowIndex";

	private LogHandle				fLog;
	
	public SVDBShadowIndexFactory() {
		fLog = LogFactory.getLogHandle("SVDBShadowIndexFactory");
	}
	

	public ISVDBIndex createSVDBIndex(
			String 					project_name,
			String 					base_location,
			ISVDBIndexCache			cache,
			Map<String, Object> 	config) {
		ISVDBIndex ret;
		ISVDBFileSystemProvider fs_provider = null;
		
		fLog.debug("createSVDBIndex: " + project_name + " ; " + base_location);
		
		if (base_location.startsWith("${workspace_loc}")) {
			fs_provider = new SVDBWSFileSystemProvider();
		} else {
			fs_provider = new SVDBFSFileSystemProvider();
		}

		ret = new SVDBShadowIndex(project_name, base_location, 
				fs_provider, cache, config);
		
		return ret;
	}
	
}
