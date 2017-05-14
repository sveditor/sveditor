package net.sf.sveditor.ui.explorer;

import org.eclipse.core.runtime.IAdaptable;

import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;

public class DeclCacheItem implements IProjectPathsData, IAdaptable {
	private IProjectPathsData		fParent;
	protected SVDBDeclCacheItem		fItem;
	
	public DeclCacheItem(
			IProjectPathsData 		p,
			SVDBDeclCacheItem		item) {
		fParent = p;
		fItem = item;
	}

	@Override
	public String getName() {
		return fItem.getName();
	}
	
	public void reset() { }
	
	
	public SVDBDeclCacheItem getItem() {
		return fItem;
	}

	@Override
	public Object getParent(Object element) {
		return fParent;
	}

	@Override
	public Object[] getChildren(Object parent) {
		return ProjectPathsContentProvider.NO_ELEMENTS;
	}
	
	@Override
	public boolean hasChildren() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	@SuppressWarnings({"rawtypes","unchecked"})
	public Object getAdapter(Class adapter) {
		if (adapter == SVDBDeclCacheItem.class) {
			return fItem;
		}
		return null;
	}
	
	

}
