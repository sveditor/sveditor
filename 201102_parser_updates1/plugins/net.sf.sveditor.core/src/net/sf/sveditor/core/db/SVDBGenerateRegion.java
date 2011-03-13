package net.sf.sveditor.core.db;

import java.util.ArrayList;
import java.util.List;

public class SVDBGenerateRegion extends SVDBChildItem implements ISVDBScopeItem {
	private List<ISVDBItemBase>			fGenerateItems;
	private SVDBLocation				fEndLocation;
	
	public SVDBGenerateRegion() {
		super(SVDBItemType.GenerateRegion);
		fGenerateItems = new ArrayList<ISVDBItemBase>();
	}

	public Iterable<ISVDBItemBase> getChildren() {
		return fGenerateItems;
	}

	public SVDBLocation getEndLocation() {
		return fEndLocation;
	}

	public void setEndLocation(SVDBLocation loc) {
		fEndLocation = loc;
	}

	public List<ISVDBItemBase> getItems() {
		return fGenerateItems;
	}

}
