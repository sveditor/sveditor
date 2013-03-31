package net.sf.sveditor.core.db.index;

public class SVDBIndexResourceChangeEvent {
	
	public enum Type {
		ADD,
		CHANGE,
		REMOVE
	}
	
	private String						fPath;
	private Type						fType;

	public SVDBIndexResourceChangeEvent(Type type, String path) {
		fType = type;
		fPath = path;
	}
	
	public Type getType() {
		return fType;
	}
	
	public String getPath() {
		return fPath;
	}

}
