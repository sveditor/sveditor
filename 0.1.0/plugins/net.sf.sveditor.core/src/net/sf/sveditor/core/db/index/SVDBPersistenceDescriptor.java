package net.sf.sveditor.core.db.index;

import java.io.File;

public class SVDBPersistenceDescriptor {
	private File					fDBFile;
	private String					fBaseLocation;
	
	public SVDBPersistenceDescriptor(File file, String base_location) {
		fDBFile = file;
		fBaseLocation = base_location;
	}
	
	public File getDBFile() {
		return fDBFile;
	}
	
	public String getBaseLocation() {
		return fBaseLocation;
	}
}
