package net.sf.sveditor.core.db;


/**
 * 
 * @author ballance
 *
 */
public class SVDBTypeInfoClassItem extends SVDBTypeInfo {
	private SVDBParamValueAssignList			fParamAssign;
	
	public SVDBTypeInfoClassItem() {
		this("");
	}
	
	public SVDBTypeInfoClassItem(String name) {
		super(name, SVDBItemType.TypeInfoClassItem);
	}

	public SVDBTypeInfoClassItem(String name, SVDBItemType type) {
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
		setName(item.getName());
		if (item.fParamAssign == null) {
			fParamAssign = null;
		} else {
			fParamAssign = item.fParamAssign.duplicate();
		}
	}
}
