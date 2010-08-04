package net.sf.sveditor.core.tests.index;

import java.io.File;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;

public class TestArgFileIndex extends TestCase {
	
	private File				fTmpDir;
	
	

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		fTmpDir.delete();
	}

	public void testIncludePathPriority() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/arg_file_multi_include/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fTmpDir);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", 
				"${workspace_loc}/project/arg_file_multi_include/arg_file_multi_include.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem class1_dir1 = null, class1_dir2 = null;
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			System.out.println("Item: " + tmp_it.getType() + " " + tmp_it.getName());
			
			if (tmp_it.getName().equals("class1_dir1")) {
				class1_dir1 = tmp_it;
			} else if (tmp_it.getName().equals("class1_dir2")) {
				class1_dir2 = tmp_it;
			}
		}
		
		assertNull("Incorrectly found class1_dir2", class1_dir2);
		assertNotNull("Failed to find class1_dir1", class1_dir1);
	}

}
