package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBTypeInfoBuiltinNet extends SVDBTypeInfoBuiltin {
	
	private String					fWireType;
	
	public SVDBTypeInfoBuiltinNet(String wire_type, String typename) {
		super(typename, SVDBDataType.WireBuiltin);
		fWireType = wire_type;
	}
	
	public SVDBTypeInfoBuiltinNet(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fDataType = SVDBDataType.WireBuiltin;
		fWireType = reader.readString();
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeString(fWireType);
	}

	public String getWireType() {
		return fWireType;
	}
	

}
