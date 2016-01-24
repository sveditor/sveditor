package net.sf.sveditor.core.db.index.external;

import java.io.File;
import java.io.IOException;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileIndexCacheMgr;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystem;

/**
 * - Need to break down the ArgFileIndex
 * -> Need to be able to perform operations 
 * @author ballance
 *
 */

public class ExternalIndexer {
	private SVDBFileSystem				fFS;
	
	public ExternalIndexer(File fs_path) {
		fFS = new SVDBFileSystem(fs_path, SVCorePlugin.getVersion());
	
		try {
			fFS.init();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	}
	
	public void full_build() {
		
	}

	public static synchronized File createTempDir() {
		File tmpdir = new File(System.getProperty("java.io.tmpdir"));
		File ret = null; 
		
		for (int i=1; i<10000; i++) {
			File tmp = new File(tmpdir, "sveditor_tmp_" + i);
			if (!tmp.isDirectory()) {
				tmp.mkdirs();
				ret = tmp;
				break;
			}
		}
		
		return ret;
	}
	
	/**
	 * - Path to the cache filesystem
	 * - Server socket to connect to
	 * - Use special log message listener, so messages are channeled back to 'super'
	 * - Have 'super' setup initial filesystem
	 * -> Include paths
	 * -> Macro definitions
	 * -> List of files to parse
	 * - Have 'super' send build directives to 'sub'
	 * -> 
	 * -->  
	 * 
	 * - List of root files to parse
	 * - Directives (+define, +include, etc)
	 * - Filemap will need to be communicated in some form
	 * - Will want to commuicate some level of progress back
	 * - Path to cache file
	 * --> Upper level deals with argument files and path resolution
	 * --> External Indexer just processes SV files
	 * 
	 * There is an overhead to creating the persistence factory. 
	 * I'm uncertain what the overhead is. Perhaps, in the 
	 * grand scheme of things, the overhead isn't too bad.
	 * @param args
	 */
	public static final void main(String args[]) {
		String argfile = args[0];
		
		SVCorePlugin.testInit();
	
		File tmpdir = createTempDir();
		File db = new File(tmpdir, "db");
		SVDBFileSystem fs = new SVDBFileSystem(db, SVCorePlugin.getVersion());
		try {
			fs.init();
		} catch (IOException e) {
			e.printStackTrace();
		}
		SVDBFileIndexCacheMgr cache_mgr = new SVDBFileIndexCacheMgr();
		cache_mgr.init(fs);
		
		SVDBArgFileIndexFactory f = new SVDBArgFileIndexFactory();
	
		String project = "GLOBAL";
		ISVDBIndex index = new SVDBArgFileIndex(
				project,
				argfile,
				new SVDBFSFileSystemProvider(),
				cache_mgr.createIndexCache(project, argfile),
				null);
		
		index.init(new NullProgressMonitor(), null);

		System.out.println("--> rebuild");
		long start = System.currentTimeMillis();
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
//		index.rebuildIndex(new NullProgressMonitor());
		long end = System.currentTimeMillis();
		System.out.println("<-- rebuild: " + (end-start));
		
		System.out.println("--> dispose");
		start = System.currentTimeMillis();
		cache_mgr.dispose();
		end = System.currentTimeMillis();
		System.out.println("<-- dispose: " + (end-start));
	}

}
