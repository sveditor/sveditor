package net.sf.sveditor.core.db.index.old;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.SVDBShadowIndex;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.InMemoryIndexCache;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.NullProgressMonitor;

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
			SVDBIndexConfig			config) {
		ISVDBIndex ret;
		ISVDBFileSystemProvider fs_provider = null;
		
		fLog.debug("createSVDBIndex: " + project_name + " ; " + base_location);
		
		fs_provider = new SVDBWSFileSystemProvider();
		/*
		if (base_location.startsWith("${workspace_loc}")) {
		} else {
			fs_provider = new SVDBFSFileSystemProvider();
		}
		 */

		ret = new SVDBShadowIndex(project_name, base_location, 
				fs_provider, cache, config);
		
		return ret;
	}
	
	public static ISVDBIndex create(String project, String path) {
		SVDBShadowIndexFactory f = new SVDBShadowIndexFactory();
		ISVDBIndex ret = f.createSVDBIndex(project, path, new InMemoryIndexCache(), null);
		
		ret.init(new NullProgressMonitor(), SVCorePlugin.getDefault().getIndexBuilder());
		
		return ret;
	}
}
