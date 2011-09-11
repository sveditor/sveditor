package net.sf.sveditor.core.db.index;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBFileEditIndexIteratorWrapper implements ISVDBIndexIterator {
	SVDBFile								fSVDBFile;
	ISVDBIndexIterator						fIndexMgr;
	
	public SVDBFileEditIndexIteratorWrapper(SVDBFile file) {
		fSVDBFile = file;
		fIndexMgr = null;		
	}
	
	public void setIndexIterator(ISVDBIndexIterator it) {
		fIndexMgr = it;
	}
	
	public ISVDBItemIterator getItemIterator(IProgressMonitor monitor) {
		if (fIndexMgr != null) {
			SVDBIndexCollectionItemIterator it = 
				(SVDBIndexCollectionItemIterator)fIndexMgr.getItemIterator(monitor);

//			it.setOverride(fSVDBIndex, fSVDBFile);

			return it;
		} else {
			return null; // SVEmptyItemIterator;
		}
	}

	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor monitor, String name, ISVDBFindNameMatcher matcher) {
		return fIndexMgr.findGlobalScopeDecl(monitor, name, matcher);
	}

	public List<SVDBDeclCacheItem> findPackageDecl(
			IProgressMonitor monitor, SVDBDeclCacheItem pkg_item) {
		return fIndexMgr.findPackageDecl(monitor, pkg_item);
	}

	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		return fIndexMgr.getDeclFile(monitor, item);
	}
}
