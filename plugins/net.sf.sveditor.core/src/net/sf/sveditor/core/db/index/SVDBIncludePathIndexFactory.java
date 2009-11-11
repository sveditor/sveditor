package net.sf.sveditor.core.db.index;

import java.util.Map;

public class SVDBIncludePathIndexFactory implements ISVDBIndexFactory {
	
	public static final String	TYPE = "net.sf.sveditor.includePathIndex";

	public ISVDBIndex createSVDBIndex(
			String 					project_name, 
			String 					base_location,
			Map<String, Object>		config) {
		
		if (base_location.startsWith("${workspace_loc}")) {
			// TODO:
			return null;
		} else {
			return new SVDBFilesystemIncludePathIndex(project_name, base_location);
		}
	}

}
