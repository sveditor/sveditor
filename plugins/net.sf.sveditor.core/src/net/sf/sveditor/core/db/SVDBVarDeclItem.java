package net.sf.sveditor.core.db;

import java.util.List;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBVarDeclItem extends SVDBFieldItem {
	protected String						fTypeName;
	protected List<SVDBModIfcClassParam>	fParameters;
	
	public SVDBVarDeclItem(String type, String name) {
		super(name, SVDBItemType.VarDecl);
		fTypeName = type;
	}

	public SVDBVarDeclItem(String type, String name, SVDBItemType itype) {
		super(name, itype);
		fTypeName = type;
	}
	
	@SuppressWarnings("unchecked")
	public SVDBVarDeclItem(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fTypeName   = reader.readString();
		fParameters = (List<SVDBModIfcClassParam>)reader.readItemList(file, parent);
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeString(fTypeName);
		writer.writeItemList(fParameters);
	}
	
	public List<SVDBModIfcClassParam> getParameters() {
		return fParameters;
	}
	
	public void setParameters(List<SVDBModIfcClassParam> parameters) {
		fParameters = parameters;
	}

	
	public String getTypeName() {
		return fTypeName;
	}
	
	public SVDBItem duplicate() {
		SVDBVarDeclItem ret = new SVDBVarDeclItem(fTypeName, getName());
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);

		fTypeName = ((SVDBVarDeclItem)other).fTypeName;
	}

}
