package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBParamValueAssignList extends SVDBItem {
	
	private boolean							fNamedMapping;
	private List<SVDBParamValueAssign>		fParameters;
	
	public SVDBParamValueAssignList() {
		super("", SVDBItemType.ParamValueList);
		fNamedMapping = false;
		fParameters = new ArrayList<SVDBParamValueAssign>();
	}

	@SuppressWarnings("unchecked")
	public SVDBParamValueAssignList(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fNamedMapping = (reader.readInt() != 0)?true:false;
		fParameters = (List<SVDBParamValueAssign>)reader.readItemList(file, null);
	}
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItem readSVDBItem(IDBReader reader, SVDBItemType type, 
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				return new SVDBParamValueAssignList(file, parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(
				f, SVDBItemType.ParamValueList); 
	}
	
	public List<SVDBParamValueAssign> getParameters() {
		return fParameters;
	}
	
	public void addParameter(SVDBParamValueAssign assign) {
		fParameters.add(assign);
	}
	
	public boolean getIsNamedMapping() {
		return fNamedMapping;
	}
	
	public void setIsNamedMapping(boolean m) {
		fNamedMapping = m;
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeInt((fNamedMapping)?1:0);
		writer.writeItemList(fParameters);
	}

	@Override
	public SVDBItem duplicate() {
		SVDBParamValueAssignList ret = new SVDBParamValueAssignList();
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItem other) {
		super.init(other);
		
		fNamedMapping = ((SVDBParamValueAssignList)other).fNamedMapping;
		fParameters.clear();
		fParameters.addAll(((SVDBParamValueAssignList)other).fParameters);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBParamValueAssignList) {
			SVDBParamValueAssignList o = (SVDBParamValueAssignList)obj;
			
			if (o.fNamedMapping != fNamedMapping) {
				return false;
			}
			
			if (o.fParameters.size() == fParameters.size()) {
				for (int i=0; i<fParameters.size(); i++) {
					if (!fParameters.get(i).equals(o.fParameters.get(i))) {
						return false;
					}
				}
			} else {
				return false;
			}
			
			return super.equals(obj);
		}
		return false;
	}
	
}
