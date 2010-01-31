package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBTypeInfo extends SVDBItem {
	public static final int				TypeAttr_FixedArray        = (1 << 0);
	public static final int				TypeAttr_DynamicArray      = (1 << 1);
	public static final int				TypeAttr_Queue             = (1 << 2);
	public static final int				TypeAttr_AssocArray        = (1 << 3);
	public static final int				TypeAttr_ModIfc            = (1 << 4);
	public static final int				TypeAttr_Parameterized     = (1 << 5);
	public static final int				TypeAttr_Vectored          = (1 << 6);

	protected int									fAttr;
	protected List<SVDBModIfcClassParam>			fParameters;
	protected String								fVectorDim;
	protected String								fArrayDim;
	
	public SVDBTypeInfo(String typename, int attr) {
		super(typename, SVDBItemType.TypeInfo);
		fAttr = attr;
	}
	
	@SuppressWarnings("unchecked")
	public SVDBTypeInfo(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		
		fAttr = reader.readInt();
		fParameters = reader.readItemList(file, parent);
		fVectorDim  = reader.readString();
		fArrayDim   = reader.readString();
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeInt(fAttr);
		writer.writeItemList(fParameters);
		writer.writeString(fVectorDim);
		writer.writeString(fArrayDim);
	}
	
	public int getAttr() {
		return fAttr;
	}

	public List<SVDBModIfcClassParam> getParameters() {
		return fParameters;
	}
	
	public void setParameters(List<SVDBModIfcClassParam> parameters) {
		fParameters = parameters;
	}
	
	public String getVectorDim() {
		return fVectorDim;
	}
	
	public String getArrayDim() {
		return fArrayDim;
	}
	
	public void setVectorDim(String dim) {
		fVectorDim = dim;
	}
	
	public void setArrayDim(String dim) {
		fArrayDim = dim;
	}

	public SVDBItem duplicate() {
		SVDBTypeInfo ret = new SVDBTypeInfo(getName(), fAttr);
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);
		
		SVDBTypeInfo other_t = (SVDBTypeInfo)other;
		
		fAttr = other_t.fAttr;
		if (other_t.fParameters != null) {
			if (fParameters == null) {
				fParameters = new ArrayList<SVDBModIfcClassParam>();
			}
			fParameters.addAll(other_t.fParameters);
		} else {
			if (fParameters != null) {
				fParameters = null;
			}
		}
		fArrayDim    = other_t.fArrayDim;
		fVectorDim = other_t.fVectorDim;
	}

}
