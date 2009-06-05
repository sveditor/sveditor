package net.sf.sveditor.core.db.index;

import java.util.Map;

public class SVDBLibPathIndexFactory implements ISVDBIndexFactory {
	
	public static final String			TYPE = "net.sf.sveditor.libIndex";

	public ISVDBIndex createSVDBIndex(
			String 					project_name, 
			String 					base_location,
			Map<String, Object>		config) {
		ISVDBIndex ret = null;
		
		if (base_location.startsWith("${workspace_loc}")) {
			ret = new SVDBWorkspaceLibIndex(project_name, base_location);
		} else {
			ret = new SVDBFileSystemLibIndex(project_name, base_location);
		}

		return ret;
	}

}
