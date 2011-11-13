package net.sf.sveditor.core.batch;

import java.io.File;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.db.index.cache.SVDBDirFS;
import net.sf.sveditor.core.db.index.cache.SVDBFileIndexCache;

public class SVEditorVlogIndexFactory {
	
	public static ISVDBIndex vlog(String args[]) {
		return vlog_loc(System.getProperty("user.dir"), args);
	}
	
	public static ISVDBIndex vlog_loc(String location, String args[]) {
		ISVDBIndex index = null;
		StringBuilder sb = new StringBuilder();
		
		for (String arg : args) {
			arg = SVDBIndexUtil.expandVars(arg, null);
			if (arg.indexOf(' ') != -1 || arg.indexOf('\t') != -1) {
				sb.append("\"" + arg + "\"\n");
			} else {
				sb.append(arg + "\n");
			}
		}
		
		SVDBArgFileIndexFactory f = new SVDBArgFileIndexFactory();
		
		// Select a temporary directory
		File tmpdir = SVBatchPlugin.createTempDir();
		SVDBDirFS dir_fs = new SVDBDirFS(tmpdir);
		SVDBFileIndexCache index_c = new SVDBFileIndexCache(dir_fs);
		
		index = f.createSVDBIndex(null, location, sb, index_c, null);
		
		index.init(new NullProgressMonitor());
		
		return index;
	}

}
