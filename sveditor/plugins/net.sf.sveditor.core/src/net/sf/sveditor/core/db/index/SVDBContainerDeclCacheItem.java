package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;

/**
 * Simple container that implements the DeclCacheItem. Allows us to
 * temporarily 'fake' using the decl cache
 * 
 * @author ballance
 *
 */
public class SVDBContainerDeclCacheItem extends SVDBDeclCacheItem {
	private ISVDBItemBase			fItem;
	
	public SVDBContainerDeclCacheItem(ISVDBItemBase item) {
		fItem = item;
	}

	@Override
	public String getName() {
		return SVDBItem.getName(fItem);
	}

	@Override
	public SVDBItemType getType() {
		return fItem.getType();
	}

	@Override
	public ISVDBItemBase getSVDBItem() {
		return fItem;
	}

}
