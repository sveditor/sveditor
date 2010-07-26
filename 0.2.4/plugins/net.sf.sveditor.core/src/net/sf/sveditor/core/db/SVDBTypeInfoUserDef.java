package net.sf.sveditor.core.db;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;


public class SVDBTypeInfoUserDef extends SVDBTypeInfo {
	protected SVDBParamValueAssignList				fParamAssignList;
	
	public SVDBTypeInfoUserDef(String typename) {
		this(typename, SVDBDataType.UserDefined);
	}
	
	public SVDBTypeInfoUserDef(String typename, SVDBDataType type) {
		super(typename, type);
	}
	
	public SVDBTypeInfoUserDef(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(SVDBDataType.UserDefined, file, parent, type, reader);
		fParamAssignList = (SVDBParamValueAssignList)reader.readSVDBItem(file, parent);
	}
	
	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeSVDBItem(fParamAssignList);
	}

	public SVDBParamValueAssignList getParameters() {
		return fParamAssignList;
	}

	public void setParameters(SVDBParamValueAssignList params) {
		fParamAssignList = params;
	}
	
	public String toString() {
		StringBuilder ret = new StringBuilder();
		ret.append(getName());
		
		if (fParamAssignList != null && fParamAssignList.getParameters().size() > 0) {
			ret.append(" #(");
			
			for (SVDBParamValueAssign p : fParamAssignList.getParameters()) {
				if (fParamAssignList.getIsNamedMapping()) {
					ret.append("." + p.getName() + "(" + p.getValue() + "), ");
				} else {
					ret.append(p.getValue() + ", ");
				}
			}
			
			ret.setLength(ret.length()-2);
			ret.append(")");
		}
		
		return ret.toString();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBTypeInfoUserDef) {
			SVDBTypeInfoUserDef o = (SVDBTypeInfoUserDef)obj;
			
			if (fParamAssignList == null || o.fParamAssignList == null) {
				if (fParamAssignList != o.fParamAssignList) {
					return false;
				}
			} else if (fParamAssignList.equals(o.fParamAssignList)) {
				return false;
			}
			
			return super.equals(obj);
		}
		return false;
	}

	@Override
	public SVDBItem duplicate() {
		SVDBTypeInfoUserDef ret = new SVDBTypeInfoUserDef(getName(), getDataType());
		
		if (fParamAssignList != null) {
			ret.setParameters((SVDBParamValueAssignList)getParameters().duplicate());
		}
		
		return ret;
	}
	
}
