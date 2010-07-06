package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBTypeInfoFwdDecl extends SVDBTypeInfo {
	
	private String					fTypeClass; // class, enum, union, struct
	
	public SVDBTypeInfoFwdDecl(String type_class, String typename) {
		super(typename, SVDBDataType.FwdDecl);
		fTypeClass = type_class;
	}
	
	public SVDBTypeInfoFwdDecl(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(SVDBDataType.FwdDecl, file, parent, type, reader);
		fTypeClass = reader.readString();
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeString(fTypeClass);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTypeInfoFwdDecl) {
			SVDBTypeInfoFwdDecl o = (SVDBTypeInfoFwdDecl)obj;
			
			return (fTypeClass.equals(o.fTypeClass) &&
					super.equals(obj));
		}
		return false;
	}

	@Override
	public SVDBItem duplicate() {
		SVDBTypeInfoFwdDecl ret = new SVDBTypeInfoFwdDecl(fTypeClass, getName());
		
		return ret;
	}
	
}
