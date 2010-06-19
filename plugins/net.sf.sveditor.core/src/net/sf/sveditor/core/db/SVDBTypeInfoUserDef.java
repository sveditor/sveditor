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
}
