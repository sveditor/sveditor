package net.sf.sveditor.core.db.index;

import java.util.Map;

public class SVDBArgFileIndexFactory implements ISVDBIndexFactory {
	
	public static final String	TYPE = "net.sf.sveditor.argFileIndex";
	public static final String  ARG_ArgFiles = "argFileIndex.argFiles";

	public ISVDBIndex createSVDBIndex(
			String 					projectName, 
			String 					base_location,
			Map<String, Object> 	config) {
		if (base_location.startsWith("${workspace_loc}")) {
			return new SVDBWorkspaceArgFileIndex(projectName, base_location);
		} else {
			
		}
		
		return null;
	}

}
