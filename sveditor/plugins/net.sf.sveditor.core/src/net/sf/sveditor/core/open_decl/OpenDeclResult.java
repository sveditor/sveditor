package net.sf.sveditor.core.open_decl;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;

public class OpenDeclResult {

	private SVDBFile				fFile;
	private SVDBFile				fFilePP;
	private ISVDBItemBase			fItem;
	
	public OpenDeclResult(SVDBFile file, SVDBFile pp_file, ISVDBItemBase item) {
		fFile = file;
		fFilePP = pp_file;
		fItem = item;
	}
	
	public SVDBFile getFile() {
		return fFile;
	}
	
	public SVDBFile getFilePP() {
		return fFilePP;
	}
	
	public ISVDBItemBase getItem() {
		return fItem;
	}
	

}
