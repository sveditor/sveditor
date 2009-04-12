package net.sf.sveditor.core.tests;

import java.io.File;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBFilesystemIndex;

public class SVDBIndexProfiler {
	
	
	public static final void main(String args[]) {
		File root = new File(args[0]);
		
		SVDBFilesystemIndex index = new SVDBFilesystemIndex(
				root, ISVDBIndex.IT_BuildPath);
		
		try {
			Thread.sleep(30000);
		} catch (Exception e) { } 
	}
}
