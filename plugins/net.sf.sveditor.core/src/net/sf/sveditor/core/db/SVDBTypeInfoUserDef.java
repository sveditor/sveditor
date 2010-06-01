package net.sf.sveditor.core.db;


public class SVDBTypeInfoUserDef extends SVDBTypeInfo {
	protected SVDBParamValueAssignList				fParamAssignList;
	
	public SVDBTypeInfoUserDef(String typename) {
		this(typename, SVDBDataType.UserDefined);
	}
	
	public SVDBTypeInfoUserDef(String typename, SVDBDataType type) {
		super(typename, type);
	}
	
	public SVDBParamValueAssignList getParameters() {
		return fParamAssignList;
	}

	public void setParameters(SVDBParamValueAssignList params) {
		fParamAssignList = params;
	}
}
