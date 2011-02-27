package net.sf.sveditor.core.db;


/**
 * 
 * @author ballance
 *
 */
public class SVDBTypeInfoClassItem extends SVDBTypeInfo {
	private SVDBParamValueAssignList			fParamAssign;
	
	public SVDBTypeInfoClassItem(String name) {
		super(name, SVDBDataType.ClassItem);
	}

	public SVDBTypeInfoClassItem(String name, SVDBDataType type) {
		super(name, type);
	}

	public boolean hasParameters() {
		return (fParamAssign != null && fParamAssign.getParameters().size() > 0);
	}
	
	public void setParamAssignList(SVDBParamValueAssignList assign) {
		fParamAssign = assign;
	}
	
	public SVDBParamValueAssignList getParamAssignList() {
		return fParamAssign;
	}
	
	public void init_class_item(SVDBTypeInfoClassItem item) {
		if (item.fParamAssign == null) {
			fParamAssign = null;
		} else {
			fParamAssign = item.fParamAssign.duplicate();
		}
	}
}
