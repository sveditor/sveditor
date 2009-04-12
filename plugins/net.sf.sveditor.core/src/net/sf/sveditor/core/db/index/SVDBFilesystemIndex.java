package net.sf.sveditor.core.db.index;

import java.io.File;

public class SVDBFilesystemIndex extends SVDBIndexBase {
	
	public SVDBFilesystemIndex(
			File 					root, 
			int						index_type) {
		super(root, index_type);
	}
	
	
	public String getTypeID() {
		return ISVDBIndexFactory.TYPE_FilesystemIndex;
	}

	public void dispose() {
		super.dispose();
	}
	
}
