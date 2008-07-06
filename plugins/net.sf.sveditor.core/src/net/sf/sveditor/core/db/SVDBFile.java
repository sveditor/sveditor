package net.sf.sveditor.core.db;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class SVDBFile extends SVDBScopeItem {
	private long				fLastParseTimeStamp;
	private File				fFile;
	private List<SVDBMacroDef>	fMacroDefs;
	private List<String>		fInclude;
	
	public SVDBFile(File file) {
		super(file.getName(), SVDBItemType.File);
		fFile               = file;
		fLastParseTimeStamp = fFile.lastModified();
		fMacroDefs          = new ArrayList<SVDBMacroDef>();
		fInclude            = new ArrayList<String>();
	}
	
	public List<SVDBMacroDef> getMacroDefs() {
		return fMacroDefs;
	}
	
	public
	List<String> getIncludes() {
		return fInclude;
	}
	
	public boolean isUpToDate() {
		return (fFile.lastModified() <= fLastParseTimeStamp);
	}
	
	public File getFilePath() {
		return fFile;
	}
	
	public SVDBItem duplicate() {
		SVDBFile ret = new SVDBFile(fFile);
		
		ret.init(this);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);

		fFile               = ((SVDBFile)other).fFile;
		fLastParseTimeStamp = ((SVDBFile)other).fLastParseTimeStamp;
	}
	
}
