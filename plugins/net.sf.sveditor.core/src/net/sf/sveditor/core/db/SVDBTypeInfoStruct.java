package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBTypeInfoStruct extends SVDBTypeInfo {
	private List<SVDBVarDeclItem>			fFields;
	
	public SVDBTypeInfoStruct() {
		super("<<ANONYMOUS>>", SVDBDataType.Struct);
		fFields = new ArrayList<SVDBVarDeclItem>();
	}
	
	@SuppressWarnings("unchecked")
	public SVDBTypeInfoStruct(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fFields = (List<SVDBVarDeclItem>)reader.readItemList(file, parent);
	}
	
	public List<SVDBVarDeclItem> getFields() {
		return fFields;
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeItemList(fFields);
	}
	
}
