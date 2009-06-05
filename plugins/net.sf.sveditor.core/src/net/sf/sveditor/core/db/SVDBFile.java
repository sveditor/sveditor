package net.sf.sveditor.core.db;

import java.io.File;

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBFile extends SVDBScopeItem {
	private long						fLastModified;
	private String						fFile;
	
	public SVDBFile(String file) {
		super(new File(file).getName(), SVDBItemType.File);
		fFile               = file;
	}

	public SVDBFile(String file, long lastModified) {
		this(file);
		
		fLastModified = lastModified;
	}

	public SVDBFile(
			SVDBFile file, 
			SVDBScopeItem parent, 
			SVDBItemType type, 
			IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		fFile               = reader.readString();
		fLastModified 		= reader.readLong();
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeString(fFile);
		writer.writeLong(fLastModified);
	}
	
	public long getLastModified() {
		return fLastModified;
	}
	
	public void setLastModified(long lastModified) {
		fLastModified = lastModified;
	}
	
	public String getFilePath() {
		return fFile;
	}
	
	public void setFilePath(String file) {
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
		fLastModified = ((SVDBFile)other).fLastModified;
	}
	
}
