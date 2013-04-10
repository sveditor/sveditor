package net.sf.sveditor.core.db.index.cache.file;

import java.lang.ref.Reference;
import java.lang.ref.SoftReference;
import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMarker;


public class SVDBFileIndexCacheEntry {
	
	private	SVDBFileIndexCacheEntry			fPrev;
	private	SVDBFileIndexCacheEntry			fNext;
	
	private boolean							fCached;

	private SVDBFile						fSVDBFileRef;
	private Reference<SVDBFile>				fSVDBFile;

	// Obsolete
	private SVDBFile						fSVDBPreProcFileRef;
	private Reference<SVDBFile>				fSVDBPreProcFile;
	
	private SVDBFileTree					fSVDBFileTreeRef;
	private Reference<SVDBFileTree>			fSVDBFileTree;
	
	private List<SVDBMarker>				fMarkersRef;
	private Reference<List<SVDBMarker>>		fMarkers;
	
	private long							fLastModified;

	public SVDBFileIndexCacheEntry() {
	}
	
	SVDBFileIndexCacheEntry getPrev() {
		return fPrev;
	}
	
	void setPrev(SVDBFileIndexCacheEntry prev) {
		fPrev = prev;
	}

	SVDBFileIndexCacheEntry getNext() {
		return fNext;
	}
	
	void setNext(SVDBFileIndexCacheEntry next) {
		fNext = next;
	}
	
	boolean isCached() {
		return fCached;
	}

	/**
	 * clear references and set 'cached' to false
	 */
	void clearCached() {
		fSVDBFileRef = null;
		fSVDBFileTreeRef = null;
		fSVDBPreProcFileRef = null;
		fCached = false;
	}
	
	void setCached() {
		fCached = true;
		fSVDBFileRef = fSVDBFile.get();
		fSVDBFileTreeRef = fSVDBFileTree.get();
		fSVDBPreProcFileRef = fSVDBPreProcFile.get();
	}

	@SuppressWarnings("unchecked")
	void setFileTree(SVDBFileTree ft) {
		fSVDBFileTree = (Reference<SVDBFileTree>)createRef(ft);
		fSVDBFileTreeRef = ft;
	}
	
	@SuppressWarnings("unchecked")
	void setPreProcFile(SVDBFile file) {
		fSVDBPreProcFile = (Reference<SVDBFile>)createRef(file);
		fSVDBPreProcFileRef = file;
	}
	
	@SuppressWarnings("unchecked")
	void setFile(SVDBFile file) {
		fSVDBFile    = (Reference<SVDBFile>)createRef(file);
		fSVDBFileRef = file;
	}

	@SuppressWarnings({"unchecked","rawtypes"})
	private Reference createRef(Object r) {
		return new SoftReference(r);
	}
}
