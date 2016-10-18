package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.SVDBFile;

public class SVDBIndexChangeDelta {
	public enum Type {
		Add,
		Remove,
		Change
	};
	
	private Type				fType;
	private SVDBFile			fFile;
	
	public SVDBIndexChangeDelta(Type t, SVDBFile f) {
		fType = t;
		fFile = f;
	}
	
	public Type getType() { return fType; }
	
	public SVDBFile getFile() { return fFile; }

}
