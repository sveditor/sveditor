package net.sf.sveditor.core;

import java.io.File;

public class SVDBFilesystemIndex extends SVDBIndexBase {
	
	public SVDBFilesystemIndex(
			File 					root, 
			int						index_type) {
		super(root, index_type);
	}
	
	
	public void dispose() {
		super.dispose();
	}
	
}
