package net.sf.sveditor.core.parser;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBModIfcClassParam;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.db.SVDBTypeInfoClassType;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBClassDecl extends SVDBScopeItem {
	
	private List<SVDBModIfcClassParam>			fParams;
	private SVDBTypeInfoClassType				fClassType;
	private SVDBTypeInfoClassType				fSuperClass;

	public SVDBClassDecl(String name) {
		super(name, SVDBItemType.Class);
	}

	@SuppressWarnings("unchecked")
	public SVDBClassDecl(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(parent, type, reader);
		fClassType  = (SVDBTypeInfoClassType)reader.readSVDBItem(parent);
		fParams     = (List<SVDBModIfcClassParam>)reader.readItemList(this);
		fSuperClass = (SVDBTypeInfoClassType)reader.readSVDBItem(parent);
	}

	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeSVDBItem(fClassType);
		writer.writeItemList(fParams);
		writer.writeSVDBItem(fSuperClass);
	}

	public List<SVDBModIfcClassParam> getParameters() {
		return fParams;
	}
	
	public void addParameters(List<SVDBModIfcClassParam> params) {
		if (fParams == null) {
			fParams = new ArrayList<SVDBModIfcClassParam>();
		}
		fParams.addAll(params);
	}
	
	public SVDBTypeInfoClassType getClassType() {
		return fClassType;
	}
	
	public void setClassType(SVDBTypeInfoClassType cls_type) {
		fClassType = cls_type;
	}

	public SVDBTypeInfoClassType getSuperClass() {
		return fSuperClass;
	}
	
	public void setSuperClass(SVDBTypeInfoClassType super_class) {
		fSuperClass = super_class;
	}
	
	public SVDBClassDecl duplicate() {
		SVDBClassDecl ret = new SVDBClassDecl(getName());
		
		ret.init(this);
		
		return ret;
	}

	public void init(SVDBItemBase other) {
		super.init(other);
		SVDBClassDecl o = (SVDBClassDecl)other;

		if (o.fParams != null) {
			fParams.clear();
			for (SVDBModIfcClassParam p : o.fParams) {
				fParams.add((SVDBModIfcClassParam)p.duplicate());
			}
		} else {
			fParams = null;
		}
		
		setSuperClass(o.getSuperClass());
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBClassDecl) {
			SVDBClassDecl o = (SVDBClassDecl)obj;
			
			if (fParams.size() == o.fParams.size()) {
				for (int i=0; i<fParams.size(); i++) {
					SVDBModIfcClassParam p1 = fParams.get(i);
					SVDBModIfcClassParam p2 = o.fParams.get(i);
					
					if (!p1.equals(p2)) {
						return false;
					}
				}
			} else {
				return false;
			}
			
			if (fSuperClass == null || o.fSuperClass == null) {
				if (fSuperClass != o.fSuperClass) {
					return false;
				}
			} else if (!fSuperClass.equals(o.fSuperClass)) {
				return false;
			}
			
			return super.equals(obj);
		}
		return false;
	}

}
