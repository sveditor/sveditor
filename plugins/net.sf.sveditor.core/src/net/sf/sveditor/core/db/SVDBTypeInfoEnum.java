package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBTypeInfoEnum extends SVDBTypeInfo {
	private List<Tuple<String, String>>			fEnumList;
	
	public SVDBTypeInfoEnum(String typename) {
		super(typename, SVDBDataType.Enum);
		fEnumList = new ArrayList<Tuple<String,String>>();
	}

	public SVDBTypeInfoEnum(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(SVDBDataType.Enum, file, parent, type, reader);
		
		fEnumList = new ArrayList<Tuple<String,String>>();
		int size = reader.readInt();
		for (int i=0; i<size; i++) {
			fEnumList.add(new Tuple<String, String>(
					reader.readString(), reader.readString()));
		}
	}
	
	@Override
	public void dump(IDBWriter writer) {
		// TODO Auto-generated method stub
		super.dump(writer);
		
		writer.writeInt(fEnumList.size());
		for (int i=0; i<fEnumList.size(); i++) {
			writer.writeString(fEnumList.get(i).first());
			writer.writeString(fEnumList.get(i).second());
		}
	}

	public List<Tuple<String, String>> getEnumValues() {
		return fEnumList;
	}
	
	public void addEnumValue(String name, String value) {
		fEnumList.add(new Tuple<String, String>(name, value));
	}
	
	public String toString() {
		return getName();
	}

}
