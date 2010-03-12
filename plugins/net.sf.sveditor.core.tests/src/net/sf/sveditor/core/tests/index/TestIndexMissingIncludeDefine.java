package net.sf.sveditor.core.tests.index;

import java.io.File;

import org.eclipse.core.resources.IProject;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.AbstractSVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.db.index.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.tests.Activator;
import net.sf.sveditor.core.tests.SaveMarkersFileSystemProvider;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestIndexMissingIncludeDefine extends TestCase {
	
	private File					fTmpDir;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		fTmpDir = TestUtils.createTempDir();
	}
	
	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		if (fTmpDir != null) {
			fTmpDir.delete();
			fTmpDir = null;
		}
	}

	
	public void testWSLibMissingIncludeDefine() {
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		
		IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc_def/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fTmpDir);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", 
				"${workspace_loc}/project/basic_lib_missing_inc_def/basic_lib_pkg.sv", 
				SVDBLibPathIndexFactory.TYPE, null);
		
		int_TestMissingIncludeDefine(index);
	}

	public void testWSArgFileMissingIncludeDefine() {
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		
		IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc_def/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fTmpDir);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", 
				"${workspace_loc}/project/basic_lib_missing_inc_def/pkg.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		int_TestMissingIncludeDefine(index);
	}

	public void testWSSourceCollectionMissingIncludeDefine() {
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		
		IProject project_dir = TestUtils.createProject("ws_sc_project");
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc_def/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fTmpDir);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", 
				"${workspace_loc}/ws_sc_project/basic_lib_missing_inc_def",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		int_TestMissingIncludeDefine(index);
	}

	public void int_TestMissingIncludeDefine(
			ISVDBIndex					index) {
		SaveMarkersFileSystemProvider fs_provider_m = new SaveMarkersFileSystemProvider(
					((AbstractSVDBIndex)index).getFileSystemProvider());
		((AbstractSVDBIndex)index).setFileSystemProvider(fs_provider_m);
		
		SVCorePlugin.getDefault().enableDebug(true);
		
		// Force the file database to be built
		index.getFileDB();
		
		assertEquals("Expecting a total of two errors", 
				2, fs_provider_m.getMarkers().size());
	}

}
