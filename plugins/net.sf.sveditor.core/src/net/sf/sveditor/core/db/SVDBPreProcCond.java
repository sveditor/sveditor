package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;


public class SVDBPreProcCond extends SVDBScopeItem {
	
	private String						fConditional;
	
	public SVDBPreProcCond(String name, String conditional) {
		super(name, SVDBItemType.PreProcCond);
		fConditional = conditional;
	}
	
	public SVDBPreProcCond(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fConditional = reader.readString();
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		System.out.println("dump pre-proc conditional \"" + getName() + "\" - " 
				+ fConditional);
		writer.writeString(fConditional);
	}
	
	
	public String getConditional() {
		return fConditional;
	}
	
	public SVDBItem duplicate() {
		SVDBPreProcCond ret = new SVDBPreProcCond(getName(), fConditional);
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);
	}
	
	public boolean equals(Object obj) {
		if (super.equals(obj) && obj instanceof SVDBPreProcCond) {
			return fConditional.equals(((SVDBPreProcCond)obj).fConditional);
		}
		return false;
	}
}
