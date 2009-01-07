package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBScopeItem extends SVDBItem {
	protected List<SVDBItem>			fItems;
	protected SVDBLocation				fEndLocation;
	
	public SVDBScopeItem(String name, SVDBItemType type) {
		super(name, type);
		
		fItems = new ArrayList<SVDBItem>();
	}
	
	public void setEndLocation(SVDBLocation loc) {
		fEndLocation = loc;
	}
	
	public SVDBLocation getEndLocation() {
		return fEndLocation;
	}
	
	public void addItem(SVDBItem item) {
		item.setParent(this);
		fItems.add(item);
	}
	
	public List<SVDBItem> getItems() {
		return fItems;
	}

	public SVDBItem duplicate() {
		SVDBScopeItem ret = new SVDBScopeItem(getName(), getType());

		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);
		
		SVDBScopeItem si = (SVDBScopeItem)other;
		
		fItems.clear();
		for (SVDBItem it : si.getItems()) {
			fItems.add(it.duplicate());
		}
		fEndLocation = new SVDBLocation(
				((SVDBScopeItem)other).fEndLocation);
	}
	
}
