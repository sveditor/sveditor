package net.sf.sveditor.core.tests;

import java.io.File;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.src_collection.SVDBFilesystemSourceCollectionIndex;
import net.sf.sveditor.core.db.index.src_collection.SVDBSourceCollectionIndexFactory;

public class SVDBIndexProfiler {
	
	
	public static final void main(String args[]) {
		File root = new File(args[0]);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", args[0],
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		try {
			Thread.sleep(30000);
		} catch (Exception e) { } 
	}
}
