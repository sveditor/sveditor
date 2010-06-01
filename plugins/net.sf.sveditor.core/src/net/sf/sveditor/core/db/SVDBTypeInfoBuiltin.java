package net.sf.sveditor.core.db;

public class SVDBTypeInfoBuiltin extends SVDBTypeInfo {
	public static final int				TypeAttr_Signed				= (1 << 7);
	public static final int				TypeAttr_Unsigned			= (1 << 8);

	private int						fAttr;
	private String					fVectorDim;
	
	public SVDBTypeInfoBuiltin(String typename) {
		super(typename, SVDBDataType.BuiltIn);
	}
	
	public int getAttr() {
		return fAttr;
	}
	
	public void setAttr(int attr) {
		fAttr = attr;
	}
	
	public String getVectorDim() {
		return fVectorDim;
	}
	
	public void setVectorDim(String dim) {
		fVectorDim = dim;
	}

}
