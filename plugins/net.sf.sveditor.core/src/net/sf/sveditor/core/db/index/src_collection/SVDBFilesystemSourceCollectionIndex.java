package net.sf.sveditor.core.db.index.src_collection;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;

public class SVDBFilesystemSourceCollectionIndex extends AbstractSVDBSourceCollectionIndex {
	
	public SVDBFilesystemSourceCollectionIndex(
			String					project,
			String 					root,
			int						index_type,
			AbstractSVFileMatcher	file_matcher) {
		super(project, root, index_type, file_matcher);
	}
	
	public String getTypeID() {
		return SVDBSourceCollectionIndexFactory.TYPE;
	}

	@Override
	protected InputStream openStream(String path) {
		InputStream in = null;
		
		try {
			in = new FileInputStream(path);
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return in;
	}

	@Override
	protected long getLastModifiedTime(String path) {
		File f = new File(path);
		
		return f.lastModified();
	}
}
