package net.sf.sveditor.core.parser;

public class SVTaskFuncParam {
	
	private String					fName;
	private String					fTypeName;
	
	public SVTaskFuncParam(String type, String name) {
		fTypeName = type;
		fName     = name;
	}
	
	public String getName() {
		return fName;
	}
	
	public String getTypeName() {
		return fTypeName;
	}
}
