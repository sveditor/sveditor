package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SVDBBaseIndexCacheData {
	private List<String>					fIncludePathList;
	private Map<String, String>				fGlobalDefines;
	private Map<String, String>				fDefineMap;

	public SVDBBaseIndexCacheData() {
		fIncludePathList = new ArrayList<String>();
		fGlobalDefines = new HashMap<String, String>();
		fDefineMap = new HashMap<String, String>();
	}
	
	public void setGlobalDefine(String key, String val) {
		if (fGlobalDefines.containsKey(key)) {
			fGlobalDefines.remove(key);
		}
		fGlobalDefines.put(key, val);
	}
	
	public Map<String, String> getGlobalDefines() {
		return fGlobalDefines;
	}
	
	public void clearGlobalDefines() {
		fGlobalDefines.clear();
	}

	public void clearDefines() {
		fDefineMap.clear();
		fDefineMap.putAll(fGlobalDefines);
	}
	
	public void addDefine(String key, String val) {
		if (fDefineMap.containsKey(key)) {
			fDefineMap.remove(key);
		}
		fDefineMap.put(key, val);
	}
	
	public Map<String, String> getDefines() {
		return fDefineMap;
	}
	
	public void clearIncludePaths() {
		fIncludePathList.clear();
	}
	
	public void addIncludePath(String path) {
		fIncludePathList.add(path);
	}
	
	public List<String> getIncludePaths() {
		return fIncludePathList;
	}
}
