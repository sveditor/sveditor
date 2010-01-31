package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBFieldItem extends SVDBItem implements IFieldItemAttr {
	
	protected int					fFieldAttr;
	
	public SVDBFieldItem(String name, SVDBItemType type) {
		super(name, type);
	}
	
	public SVDBFieldItem(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fFieldAttr = reader.readInt();
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeInt(fFieldAttr);
	}
	
	public int getAttr() {
		return fFieldAttr;
	}
	
	public void setAttr(int attr) {
		fFieldAttr = attr;
	}
	
	public SVDBItem duplicate() {
		SVDBFieldItem ret = new SVDBFieldItem(getName(), getType());
		
		ret.init(this);
		
		return ret;
	}
	
	public boolean equals(Object obj) {
		if (!super.equals(obj)) {
			return false;
		} else {
			return (fFieldAttr == ((SVDBFieldItem)obj).fFieldAttr);
		}
	}

	public void init(SVDBItem other) {
		super.init(other);
		
		fFieldAttr = ((SVDBFieldItem)other).fFieldAttr;
	}

}
