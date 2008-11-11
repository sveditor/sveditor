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
	private List<SVDBFile>				fFileRefs;
	
	public SVDBFile(File file) {
		super(file.getName(), SVDBItemType.File);
		fFile               = file;
		fLastParseTimeStamp = fFile.lastModified();
		fMacroDefs			= new HashMap<String, SVDBMacroDef>();
		fFileRefs			= new ArrayList<SVDBFile>();
	}
	
	
	
	public Map<String, SVDBMacroDef> getMacroDefs() {
		return fMacroDefs;
	}
	
	public SVDBMacroDef getMacroDef(String key) {
		if (fMacroDefs.containsKey(key)) {
			return fMacroDefs.get(key);
		} else {
			List<SVDBFile> files = new ArrayList<SVDBFile>();
			
			return getMacroDef(key, files);
		}
	}
	
	public void addFileRef(SVDBFile file) {
		fFileRefs.add(file);
	}
	
	private SVDBMacroDef getMacroDef(String key, List<SVDBFile> files) {
		files.add(this);
		
		if (fMacroDefs.containsKey(key)) {
			System.out.println("macroDef \"" + key + "\" in " +
					fFile.getAbsolutePath());
			return fMacroDefs.get(key);
		} else {
			for (SVDBFile f : fFileRefs) {
				if (!files.contains(f)) {
					return f.getMacroDef(key, files);
				}
			}
		}
		
		return null;
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
