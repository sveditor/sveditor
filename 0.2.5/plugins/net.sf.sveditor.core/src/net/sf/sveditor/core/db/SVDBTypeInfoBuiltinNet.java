package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBTypeInfoBuiltinNet extends SVDBTypeInfo {
	
	private String					fWireType;
	private SVDBTypeInfo			fType;
	
	public SVDBTypeInfoBuiltinNet(String wire_type, SVDBTypeInfo type) {
		super(wire_type, SVDBDataType.WireBuiltin);
		fWireType = wire_type;
		fType     = type;
	}
	
	public SVDBTypeInfoBuiltinNet(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(SVDBDataType.WireBuiltin, file, parent, type, reader);
		fWireType = reader.readString();
		fType     = (SVDBTypeInfo)reader.readSVDBItem(file, parent);
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeString(fWireType);
		writer.writeSVDBItem(fType);
	}

	public String getWireType() {
		return fWireType;
	}
	
	public SVDBTypeInfo getTypeInfo() {
		return fType;
	}
}
