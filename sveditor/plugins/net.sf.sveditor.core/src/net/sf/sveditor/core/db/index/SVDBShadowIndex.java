package net.sf.sveditor.core.db.index;

import java.io.InputStream;
import java.util.List;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.old.AbstractSVDBIndex;
import net.sf.sveditor.core.db.index.old.SVDBShadowIndexFactory;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBShadowIndex extends AbstractSVDBIndex {
	
	public SVDBShadowIndex(String project, String base_location,
			ISVDBFileSystemProvider fs_provider, ISVDBIndexCache cache,
			SVDBIndexConfig config) {
		super(project, base_location, fs_provider, cache, config);
		fPropagateMarkers = false;
	}

	public String getTypeID() {
		return SVDBShadowIndexFactory.TYPE;
	}

	@Override
	protected String getLogName() {
		return "SVDBShadowIndex";
	}
	

	@Override
	public Tuple<SVDBFile, SVDBFile> parse(IProgressMonitor monitor,
			InputStream in, String path, List<SVDBMarker> markers) {
		return super.parse(monitor, in, path, markers);
	}

	@Override
	protected void discoverRootFiles(IProgressMonitor monitor) {
		fLog.debug(LEVEL_MIN, "discoverRootFiles");

		addFile(getResolvedBaseLocation(), false);
		addIncludePath(SVFileUtils.getPathParent(getResolvedBaseLocation()));
	}

}
