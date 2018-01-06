package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBFileOverrideDeclCacheItem extends SVDBDeclCacheItem {
	private SVDBFileOverrideIndex		fIndex;
	private ISVDBItemBase				fItem;
	private SVDBItemType				fType;
	private String						fName;
	private boolean						fIsFtItem;
	
	public SVDBFileOverrideDeclCacheItem(
			SVDBItemType			type,
			String					name) {
		fType = type;
		fName = name;
	}
	
	public SVDBFileOverrideDeclCacheItem(
			SVDBFileOverrideIndex		index,
			ISVDBItemBase				item,
			boolean						is_ft
			) {
		fIndex = index;
		fItem = item;
		fIsFtItem = is_ft;
	}

	@Override
	public SVDBItemType getType() {
		return (fItem != null)?fItem.getType():fType;
	}

	@Override
	public ISVDBItemBase getSVDBItem() {
		return fItem;
	}

	@Override
	public String getName() {
		return (fName != null)?fName:((ISVDBNamedItem)fItem).getName();
	}

}
