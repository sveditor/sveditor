package net.sf.sveditor.core.db.index;

import java.util.Map;

public class SVDBIndexFactoryUtils {
	
	@SuppressWarnings("unchecked")
	public static void setBaseProperties(
			Map<String, Object>		config,
			ISVDBIndex				index) {
		if (config != null) {
			if (config.containsKey(ISVDBIndexFactory.KEY_GlobalDefineMap)) {
				Map<String, String> define_map = (Map<String, String>)
					config.get(ISVDBIndexFactory.KEY_GlobalDefineMap);
				
				for (String key : define_map.keySet()) {
					index.setGlobalDefine(key, define_map.get(key));
				}
			}
		}
	}

}
