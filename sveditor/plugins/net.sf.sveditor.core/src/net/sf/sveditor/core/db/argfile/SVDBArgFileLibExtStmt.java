package net.sf.sveditor.core.db.argfile;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBArgFileLibExtStmt extends SVDBArgFileStmt {
	
	public List<String>					fLibExtList;
	
	public SVDBArgFileLibExtStmt() {
		super(SVDBItemType.ArgFileLibExtStmt);
		
		fLibExtList = new ArrayList<String>();
	}
	
	public void addLibExt(String ext) {
		fLibExtList.add(ext);
	}
	
	public List<String> getLibExtList() {
		return fLibExtList;
	}
	

}
