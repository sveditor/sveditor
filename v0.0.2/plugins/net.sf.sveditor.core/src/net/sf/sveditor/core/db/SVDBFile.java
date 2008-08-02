package net.sf.sveditor.core.db;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class SVDBFile extends SVDBScopeItem {
	private long				fLastParseTimeStamp;
	private File				fFile;
	private List<SVDBMacroDef>	fMacroDefs;
	
	public SVDBFile(File file) {
		super(file.getName(), SVDBItemType.File);
		fFile               = file;
		fLastParseTimeStamp = fFile.lastModified();
		fMacroDefs          = new ArrayList<SVDBMacroDef>();
	}
	
	public List<SVDBMacroDef> getMacroDefs() {
		return fMacroDefs;
	}
	
	public boolean isUpToDate() {
		return (fFile.lastModified() <= fLastParseTimeStamp);
	}
	
	public File getFilePath() {
		return fFile;
	}
	
	@Override
	public void addItem(SVDBItem item) {
		super.addItem(item);
		
		if (item.getType() == SVDBItemType.Include) {
		} else if (item.getType() == SVDBItemType.Macro) {
			fMacroDefs.add((SVDBMacroDef)item);
		}
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
