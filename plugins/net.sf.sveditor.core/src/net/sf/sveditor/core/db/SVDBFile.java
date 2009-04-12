package net.sf.sveditor.core.db;

import java.io.File;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBFile extends SVDBScopeItem {
	private long						fLastParseTimeStamp;
	private File						fFile;
	
	public SVDBFile(File file) {
		super(file.getName(), SVDBItemType.File);
		fFile               = file;
		fLastParseTimeStamp = fFile.lastModified();
	}
	
	public SVDBFile(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fFile               = new File(reader.readString());
		fLastParseTimeStamp = reader.readLong();
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeString(fFile.getPath());
		writer.writeLong(fLastParseTimeStamp);
	}
	
	
	public long getLastParseTime() {
		return fLastParseTimeStamp;
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
