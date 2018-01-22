package net.sf.sveditor.core.open_decl;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;

public class OpenDeclResult {

	private SVDBFile				fFile;
	private ISVDBItemBase			fItem;
	
	public OpenDeclResult(SVDBFile file, ISVDBItemBase item) {
		fFile = file;
		fItem = item;
	}
	
	public SVDBFile getFile() {
		return fFile;
	}
	
	public ISVDBItemBase getItem() {
		return fItem;
	}
	

}
