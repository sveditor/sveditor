package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBMacroDef extends SVDBItem {
	
	private List<String>			fParams;
	private String					fDef;
	
	public SVDBMacroDef(
			String 				name, 
			List<String>		params,
			String				def) {
		super(name, SVDBItemType.Macro);
		fParams = new ArrayList<String>();
		fParams.addAll(params);
		fDef = def;
	}
	
	public SVDBMacroDef(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fParams = reader.readStringList();
		fDef    = reader.readString();
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeStringList(fParams);
		writer.writeString(fDef);
	}
	
	
	public String getDef() {
		return fDef;
	}
	
	public void setDef(String def) {
		fDef = def;
	}
	
	public List<String> getParameters() {
		return fParams;
	}

	@Override
	public SVDBItem duplicate() {
		SVDBMacroDef ret = new SVDBMacroDef(
				getName(), fParams, fDef);
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItem other) {
		super.init(other);
		
		SVDBMacroDef m = (SVDBMacroDef)other;
		fParams.clear();
		fParams.addAll(m.fParams);
		fDef = m.fDef;
	}
	
}
