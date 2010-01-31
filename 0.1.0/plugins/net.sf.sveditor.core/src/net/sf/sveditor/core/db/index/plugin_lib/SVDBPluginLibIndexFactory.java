package net.sf.sveditor.core.db.index.plugin_lib;

import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexFactory;

public class SVDBPluginLibIndexFactory implements ISVDBIndexFactory {
	
	public static final String			TYPE = "net.sf.sveditor.pluginLibIndex"; 

	public ISVDBIndex createSVDBIndex(
			String 					project, 
			String 					base_location,
			Map<String, Object>		config) {
		for (SVDBPluginLibDescriptor d : SVCorePlugin.getDefault().getPluginLibList()) {
			if (d.getId().equals(base_location)) {
				return new SVDBPluginLibIndex(project, d.getNamespace(), d.getPath());
			}
		}
		
		return null;
	}

}
