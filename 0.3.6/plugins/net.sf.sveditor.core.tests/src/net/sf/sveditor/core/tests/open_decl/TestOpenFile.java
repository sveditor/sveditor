package net.sf.sveditor.core.tests.open_decl;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibIndex;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestOpenFile extends TestCase {
	
	
	public void testRelPathOpenDecl() throws IOException {
		File tmpdir = TestUtils.createTempDir();
		SVCorePlugin.getDefault().enableDebug(false);
		
		try {
			BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

			utils.copyBundleDirToFS("/data/pkg_rel_path_include/", tmpdir);
			
			File subdir2 = new File(tmpdir, "pkg_rel_path_include/subdir1/subdir2");
			
			TestUtils.createProject("subdir2", subdir2);
			
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			rgy.init(null);
			
			ISVDBIndex target_index = rgy.findCreateIndex("subdir2",
					"${workspace_loc}/subdir2/pkg_rel_path_include.sv",
					SVDBLibPathIndexFactory.TYPE, null);

			ISVDBItemIterator it = target_index.getItemIterator();
			ISVDBFileSystemProvider fs_provider = 
				((SVDBLibIndex)target_index).getFileSystemProvider();
			
			SVDBFile file = null;
			while (it.hasNext()) {
				SVDBItem it_t = it.nextItem();
				if (it_t.getName().endsWith("pkg_rel_path_include.sv")) {
					file = (SVDBFile)it_t;
				}
			}
			
			InputStream in = fs_provider.openStream("${workspace_loc}/subdir2/pkg_rel_path_include.sv");
			String content = SVCoreTestsPlugin.readStream(in);
			StringBIDITextScanner scanner = new StringBIDITextScanner(content);
			scanner.seek(content.indexOf("target_inc_file.svh")+1);
			fs_provider.closeStream(in);
			
			List<Tuple<SVDBItem, SVDBFile>> ret = OpenDeclUtils.openDecl(
					file, 4, scanner, target_index);
			
			assertEquals(1, ret.size());
			
			System.out.println("ret.size=" + ret.size());
			
			System.out.println("File Path: " + ret.get(0).first().getName());
			
			
		} finally {
			tmpdir.delete();
		}
	}

}
