package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBGenerateRegion extends SVDBChildItem implements ISVDBScopeItem {
	private List<ISVDBChildItem>		fGenerateItems;
	private SVDBLocation				fEndLocation;
	
	public SVDBGenerateRegion() {
		super(SVDBItemType.GenerateRegion);
		fGenerateItems = new ArrayList<ISVDBChildItem>();
	}

	public Iterable<ISVDBChildItem> getChildren() {
		return fGenerateItems;
	}

	public SVDBLocation getEndLocation() {
		return fEndLocation;
	}

	public void setEndLocation(SVDBLocation loc) {
		fEndLocation = loc;
	}

	public List<ISVDBItemBase> getItems() {
		return (List<ISVDBItemBase>)((List)fGenerateItems);
	}

	public void addChildItem(ISVDBChildItem item) {
		item.setParent(this);
		fGenerateItems.add(item);
	}

	public void addItem(ISVDBItemBase item) {
		if (item instanceof ISVDBChildItem) {
			((ISVDBChildItem)item).setParent(this);
			fGenerateItems.add((ISVDBChildItem)item);
		}
	}

}
