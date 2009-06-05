package net.sf.sveditor.core.db.index;

import java.util.Map;


public interface ISVDBIndexFactory {
	
	/*
	String TYPE_WorkspaceIndex  = "net.sf.sveditor.workspaceIndex";
	String TYPE_FilesystemIndex = "net.sf.sveditor.fileSystemIndex";
	String TYPE_PluginLibIndex  = "net.sf.sveditor.pluginLibIndex";
	// String TYPE_PackageLibIndex = "net.sf.sveditor.packageLibIndex";
	 */
	
	
	ISVDBIndex createSVDBIndex(
			String 					project_name, 
			String 					base_location,
			Map<String, Object>		config);

}
