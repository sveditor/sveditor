package net.sf.sveditor.core.db.index.src_collection;

import java.io.InputStream;
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexFactory;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.db.project.SVDBSourceCollection;
import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;
import net.sf.sveditor.core.fileset.SVFileSet;
import net.sf.sveditor.core.fileset.SVFilesystemFileMatcher;
import net.sf.sveditor.core.fileset.SVWorkspaceFileMatcher;

public class SVDBSourceCollectionIndexFactory implements ISVDBIndexFactory {
	
	public static final String	TYPE = "net.sf.sveditor.sourceCollectionIndex";
	public static final String  FILESET = "FILE_SET";

	public ISVDBIndex createSVDBIndex(String project_name,
			String base_location, Map<String, Object> config) {
		ISVDBIndex ret;
		ISVDBFileSystemProvider fs_provider = null;
		
		System.out.println("createSVDBIndex: " + project_name + " ; " + base_location);
		
		SVFileSet fs = null;
		AbstractSVFileMatcher matcher = null;
		
		if (config != null) {
			fs = (SVFileSet)config.get(FILESET);
		}
		
		if (base_location.startsWith("${workspace_loc}")) {
			
			if (fs == null) {
				// Create a default fileset
				fs = new SVFileSet(base_location);
				fs.getIncludes().addAll(SVDBSourceCollection.parsePatternList(
						SVCorePlugin.getDefault().getDefaultSourceCollectionIncludes()));
				fs.getExcludes().addAll(SVDBSourceCollection.parsePatternList(
						SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes()));
			}
			
			matcher = new SVWorkspaceFileMatcher();
			matcher.addFileSet(fs);
			
			fs_provider = new SVDBFSFileSystemProvider();
			
		} else {
			if (fs == null) {
				// Create a default fileset
				fs = new SVFileSet(base_location);
				fs.getIncludes().addAll(SVDBSourceCollection.parsePatternList(
						SVCorePlugin.getDefault().getDefaultSourceCollectionIncludes()));
				fs.getExcludes().addAll(SVDBSourceCollection.parsePatternList(
						SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes()));
			}
			
			matcher = new SVFilesystemFileMatcher();
			matcher.addFileSet(fs);
			
			fs_provider = new SVDBWSFileSystemProvider();
		}

		ret = new SVDBSourceCollectionIndex(
				project_name, base_location, ISVDBIndex.IT_BuildPath, matcher, fs_provider);
		
		return ret;
	}

}
