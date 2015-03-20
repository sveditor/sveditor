package net.sf.sveditor.core.tagproc;

import java.util.HashMap;
import java.util.Map;

public class TemplateParameterProvider implements ITemplateParameterProvider {
	private Map<String, String>			fTagMap;
	
	public TemplateParameterProvider() {
		fTagMap = new HashMap<String, String>();
	}

	public TemplateParameterProvider(Map<String, String> init) {
		this();
		fTagMap.putAll(init);
	}

	public TemplateParameterProvider(TemplateParameterProvider init) {
		this();
		fTagMap.putAll(init.fTagMap);
	}

	public boolean providesParameter(String id) {
		return fTagMap.containsKey(id);
	}

	public String getParameterValue(String id, String arg) {
		return getTag(id);
	}

	public void setTag(String tag, String value) {
		if (fTagMap.containsKey(tag)) {
			fTagMap.remove(tag);
		}
		fTagMap.put(tag, value);
	}

	public void removeTag(String tag) {
		fTagMap.remove(tag);
	}

	public boolean hasTag(String tag) {
		return fTagMap.containsKey(tag);
	}

	public String getTag(String tag) {
		return fTagMap.get(tag);
	}
	
	public void appendTag(String tag, String value) {
		String val;
		if (fTagMap.containsKey(tag)) {
			val = fTagMap.get(tag);
			fTagMap.remove(tag);
		} else {
			val = "";
		}
		val += value;
		fTagMap.put(tag, val);
	}
	
}
