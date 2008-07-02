package net.sf.sveditor.core.db;

import java.io.File;

public class SVDBFile extends SVDBScopeItem {
	private long				fLastParseTimeStamp;
	private File				fFile;
	
	public SVDBFile(File file) {
		super(file.getName(), SVDBItemType.File);
		fFile = file;
		fLastParseTimeStamp = fFile.lastModified();
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
