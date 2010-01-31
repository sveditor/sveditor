package net.sf.sveditor.core.db.index;

import java.util.Map;

public class SVDBLibPathIndexFactory implements ISVDBIndexFactory {
	
	public static final String			TYPE = "net.sf.sveditor.libIndex";

	public ISVDBIndex createSVDBIndex(
			String 					project_name, 
			String 					base_location,
			Map<String, Object>		config) {
		ISVDBFileSystemProvider fs_provider;
		
		if (base_location.startsWith("${workspace_loc}")) {
			fs_provider = new SVDBWSFileSystemProvider();
		} else {
			fs_provider = new SVDBFSFileSystemProvider();
		}
		
		return new SVDBLibIndex(
				project_name, base_location, fs_provider);
	}

}
