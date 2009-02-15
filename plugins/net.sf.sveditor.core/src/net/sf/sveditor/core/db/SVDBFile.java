package net.sf.sveditor.core.db;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class SVDBFile extends SVDBScopeItem {
	private long						fLastParseTimeStamp;
	private File						fFile;
	private Map<String, SVDBMacroDef>	fMacroDefs;
	
	public SVDBFile(File file) {
		super(file.getName(), SVDBItemType.File);
		fFile               = file;
		fLastParseTimeStamp = fFile.lastModified();
		fMacroDefs			= new HashMap<String, SVDBMacroDef>();
	}
	
	
	
	public Map<String, SVDBMacroDef> getMacroDefs() {
		return fMacroDefs;
	}
	
	public boolean isUpToDate() {
		return (fFile.lastModified() <= fLastParseTimeStamp);
	}
	
	public File getFilePath() {
		return fFile;
	}
	
	public void setFilePath(File file) {
		fFile = file;
	}
	
	@Override
	public void addItem(SVDBItem item) {
		super.addItem(item);
		
		if (item.getType() == SVDBItemType.Include) {
		} else if (item.getType() == SVDBItemType.Macro) {
			if (fMacroDefs.containsKey(((SVDBMacroDef)item).getName())) {
				fMacroDefs.remove(((SVDBMacroDef)item).getName());
			}
			fMacroDefs.put(((SVDBMacroDef)item).getName(), (SVDBMacroDef)item); 
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
