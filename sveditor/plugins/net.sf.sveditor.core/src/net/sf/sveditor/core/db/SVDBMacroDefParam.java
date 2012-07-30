package net.sf.sveditor.core.db;

public class SVDBMacroDefParam extends SVDBChildItem implements ISVDBNamedItem {
	
	public String			fName;
	public String			fValue;

	public SVDBMacroDefParam() {
		super(SVDBItemType.MacroDefParam);
	}
	
	public SVDBMacroDefParam(String name, String value) {
		this();
		fName = name;
		fValue = value;
	}

	public String getName() {
		return fName;
	}
	
	public String getValue() {
		return fValue;
	}

}
