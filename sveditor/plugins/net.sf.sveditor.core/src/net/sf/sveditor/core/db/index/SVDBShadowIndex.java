package net.sf.sveditor.core.db.index;

import java.util.Map;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBShadowIndex extends AbstractSVDBIndex {
	
	public SVDBShadowIndex(String project, String base_location,
			ISVDBFileSystemProvider fs_provider, ISVDBIndexCache cache,
			Map<String, Object> config) {
		super(project, base_location, fs_provider, cache, config);
	}

	public String getTypeID() {
		return SVDBShadowIndexFactory.TYPE;
	}

	@Override
	protected String getLogName() {
		return "SVDBShadowIndex";
	}

	@Override
	protected void discoverRootFiles(IProgressMonitor monitor) {
		fLog.debug(LEVEL_MIN, "discoverRootFiles");

		addFile(getResolvedBaseLocation());
		addIncludePath(SVFileUtils.getPathParent(getResolvedBaseLocation()));
	}

}
