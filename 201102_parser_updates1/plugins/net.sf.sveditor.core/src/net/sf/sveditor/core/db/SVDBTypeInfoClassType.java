package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBTypeInfoClassType extends SVDBTypeInfoClassItem {
	List<SVDBTypeInfoClassItem>		fTypeInfo;
	
	public SVDBTypeInfoClassType() {
		this("");
	}
	
	public SVDBTypeInfoClassType(String name) {
		super(name, SVDBItemType.TypeInfoClassType);
	}
	
	public boolean isScoped() {
		return (fTypeInfo != null && fTypeInfo.size() > 0);
	}
	
	public void addClassItem(SVDBTypeInfoClassItem item) {
		// Push the data from this item onto the list
		// Set this to the info in the item class
		SVDBTypeInfoClassItem this_i = new SVDBTypeInfoClassItem(getName());
		this_i.init(this);
		
		if (fTypeInfo == null) {
			fTypeInfo = new ArrayList<SVDBTypeInfoClassItem>();
		}
		fTypeInfo.add(this_i);

		// Set the leaf information to the new class-item info
		init_class_item(item);
	}

}
