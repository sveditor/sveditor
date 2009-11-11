package net.sf.sveditor.core.db.index;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

public class SVDBFileSystemCompileIndex extends AbstractSVDBCompileIndex {
	
	public SVDBFileSystemCompileIndex(String project_name) {
		super(project_name);
	}
	
	@Override
	protected InputStream openStream(String path) {
		try {
			return new FileInputStream(path);
		} catch (IOException e) {}
		
		return null;
	}

	protected long getLastModifiedTime(String file) {
		File f = new File(file);
		
		return f.lastModified();
	}	

}
