package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.Tuple;

public class SVDBTypeInfoEnum extends SVDBTypeInfo {
	private List<Tuple<String, String>>			fEnumList;
	
	public SVDBTypeInfoEnum(String typename) {
		super(typename, SVDBDataType.Enum);
		fEnumList = new ArrayList<Tuple<String,String>>();
	}
	
	public List<Tuple<String, String>> getEnumValues() {
		return fEnumList;
	}
	
	public void addEnumValue(String name, String value) {
		fEnumList.add(new Tuple<String, String>(name, value));
	}

}
