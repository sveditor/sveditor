package net.sf.sveditor.core.methodology_templates;


public class MethodologyCategory {
	private String							fId;
	private String							fName;
	
	public MethodologyCategory(String id, String name) {
		fId = id;
		fName = name;
	}
	
	public String getId() {
		return fId;
	}
	
	public String getName() {
		return fName;
	}

}
