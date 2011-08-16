package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;

import org.eclipse.core.runtime.NullProgressMonitor;

public class SVDBDeclCacheItem implements ISVDBNamedItem {
	@SVDBDoNotSaveAttr
	private String						fFileName;
	
	@SVDBDoNotSaveAttr
	private ISVDBDeclCache				fParent;
	
	private String						fName;
	private SVDBItemType				fType;
	
	public SVDBDeclCacheItem() {
	}
	
	public SVDBDeclCacheItem(ISVDBDeclCache parent, String filename, String name, SVDBItemType type) {
		fParent = parent;
		fFileName = filename;
		fName = name;
		fType = type;
	}
	
	public String getFilename() {
		return fFileName;
	}
	
	public String getName() {
		return fName;
	}
	
	public void setName(String name) {
		fName = name;
	}
	
	public SVDBItemType getType() {
		return fType;
	}
	
	public void setType(SVDBItemType type) {
		fType = type;
	}
	
	public ISVDBItemBase getSVDBItem() {
		SVDBFile file = fParent.getDeclFile(new NullProgressMonitor(), this);
		
		if (file != null) {
			for (ISVDBChildItem c : file.getChildren()) {
				if (SVDBItem.getName(c).equals(fName)) {
					return c;
				}
			}
		}
		
		return null;
	}
	
}
