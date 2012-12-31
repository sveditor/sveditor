package net.sf.sveditor.core.db.argfile;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBArgFileDefineStmt extends SVDBArgFileStmt {
	public String				fKey;
	public String				fValue;
	
	public SVDBArgFileDefineStmt() {
		super(SVDBItemType.ArgFileDefineStmt);
	}
	
	public SVDBArgFileDefineStmt(String key, String val) {
		this();
		fKey = key;
		fValue = val;
	}

	public void setKey(String key) {
		fKey = key;
	}
	
	public String getKey() {
		return fKey;
	}
	
	public void setValue(String val) {
		fValue = val;
	}
	
	public String getValue() {
		return fValue;
	}
}
