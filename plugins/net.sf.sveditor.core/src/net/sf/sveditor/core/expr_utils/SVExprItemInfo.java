package net.sf.sveditor.core.expr_utils;

public class SVExprItemInfo {
	private SVExprItemType		fType;
	private String				fName;
	
	public SVExprItemInfo(
			SVExprItemType		type,
			String 				name) {
		fType = type;
		fName = name;
	}
	
	public SVExprItemType getType() {
		return fType;
	}
	
	public String getName() {
		return fName;
	}

}
