package net.sf.sveditor.core.db.index;

import java.util.Map;

public class SVDBArgFileIndexFactory implements ISVDBIndexFactory {
	
	public static final String	TYPE = "net.sf.sveditor.argFileIndex";
	public static final String  ARG_ArgFiles = "argFileIndex.argFiles";

	public ISVDBIndex createSVDBIndex(
			String 					projectName, 
			String 					base_location,
			Map<String, Object> 	config) {
		ISVDBFileSystemProvider fs_provider;
		
		if (base_location.startsWith("${workspace_loc}")) {
			fs_provider = new SVDBWSFileSystemProvider();
		} else {
			fs_provider = new SVDBFSFileSystemProvider();
		}

		return new SVDBArgFileIndex(projectName, base_location, fs_provider);
	}

}
