package net.sf.sveditor.core.tests.index.argfile2;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.BundleUtils;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import net.sf.sveditor.core.db.index.SVDBIndexResourceChangeEvent.Type;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex2;
import net.sf.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestIncrementalIndex extends SVCoreTestCaseBase {
	
	public void testRootFileChange_1() {
		String project_path = "${workspace_loc}/" + getName() + "/simple_project1";
		
		ISVDBIndex index = setupProject(
				"/data/index_file_change/simple_project1",
				project_path + "/simple_project1.f");
		
		// Now, tell the index that pkg1.sv changed, and check the plan
		List<SVDBIndexResourceChangeEvent> changes = new ArrayList<SVDBIndexResourceChangeEvent>();
		changes.add(new SVDBIndexResourceChangeEvent(Type.CHANGE, project_path + "/pkg1.sv"));
		
		ISVDBIndexChangePlan plan;
		
		plan = index.createIndexChangePlan(null);
		System.out.println("plan=" + plan);
		
		plan = index.createIndexChangePlan(changes);
		System.out.println("plan=" + plan);
		
		index.execIndexChangePlan(new NullProgressMonitor(), plan);
	}

	public void testIncFileChange_1() {
		String project_path = "${workspace_loc}/" + getName() + "/simple_project1";
		
		ISVDBIndex index = setupProject(
				"/data/index_file_change/simple_project1",
				project_path + "/simple_project1.f");
		
		IndexTestUtils.assertFileHasElements(index, "pkg1_cls1", "pkg1_cls2");
		
		// Now, change pkg1_cls1
		TestUtils.copy_ws(
				"class pkg1_cls11;\n" +
				"endclass\n",
				project_path + "/pkg1_cls1.svh");
		
		// Now, tell the index that pkg1.sv changed, and check the plan
		List<SVDBIndexResourceChangeEvent> changes = new ArrayList<SVDBIndexResourceChangeEvent>();
		changes.add(new SVDBIndexResourceChangeEvent(Type.CHANGE, project_path + "/pkg1_cls1.svh"));
		
		ISVDBIndexChangePlan plan;
		
		plan = index.createIndexChangePlan(null);
		System.out.println("plan=" + plan);
		
		plan = index.createIndexChangePlan(changes);
		System.out.println("plan=" + plan);
		
		index.execIndexChangePlan(new NullProgressMonitor(), plan);
		
		IndexTestUtils.assertFileHasElements(index, "pkg1_cls11", "pkg1_cls2");
		IndexTestUtils.assertDoesNotContain(index, "pkg1_cls1");
	}

	public void testArgFileChange_1() {
		String project_path = "${workspace_loc}/" + getName() + "/simple_project1";
		
		ISVDBIndex index = setupProject(
				"/data/index_file_change/simple_project1",
				project_path + "/simple_project1.f");
		
		// Now, tell the index that pkg1.sv changed, and check the plan
		List<SVDBIndexResourceChangeEvent> changes = new ArrayList<SVDBIndexResourceChangeEvent>();
		changes.add(new SVDBIndexResourceChangeEvent(Type.CHANGE, project_path + "/simple_project1.f"));
		
		ISVDBIndexChangePlan plan;
		
		plan = index.createIndexChangePlan(null);
		System.out.println("plan=" + plan);
		
		plan = index.createIndexChangePlan(changes);
		System.out.println("plan=" + plan);
		
		index.execIndexChangePlan(new NullProgressMonitor(), plan);
	}

	public void testIrrelevantChange_1() {
		String project_path = "${workspace_loc}/" + getName() + "/simple_project1";
		
		ISVDBIndex index = setupProject(
				"/data/index_file_change/simple_project1",
				project_path + "/simple_project1.f");
		
		// Now, tell the index that pkg1.sv changed, and check the plan
		List<SVDBIndexResourceChangeEvent> changes = new ArrayList<SVDBIndexResourceChangeEvent>();
		changes.add(new SVDBIndexResourceChangeEvent(Type.CHANGE, project_path + "/missing_file.sv"));
		
		ISVDBIndexChangePlan plan;
		
		plan = index.createIndexChangePlan(null);
		System.out.println("plan=" + plan);
		
		plan = index.createIndexChangePlan(changes);
		System.out.println("plan=" + plan);
		
		index.execIndexChangePlan(new NullProgressMonitor(), plan);
	}
	
	public void testTearDownRebuild() {
		String project_path = "${workspace_loc}/" + getName() + "/simple_project1";
		
		ISVDBIndex index = setupProject(
				"/data/index_file_change/simple_project1",
				project_path + "/simple_project1.f");
		
		// Now, tell the index that pkg1.sv changed, and check the plan
		List<SVDBIndexResourceChangeEvent> changes = new ArrayList<SVDBIndexResourceChangeEvent>();
		changes.add(new SVDBIndexResourceChangeEvent(Type.CHANGE, project_path + "/pkg1.sv"));
		
		ISVDBIndexChangePlan plan;
		
		plan = index.createIndexChangePlan(null);
		System.out.println("plan=" + plan);
		
		plan = index.createIndexChangePlan(changes);
		System.out.println("plan=" + plan);
		
		index.execIndexChangePlan(new NullProgressMonitor(), plan);
	}	
	
	private ISVDBIndex setupProject(
			String			data_dir,
			String			argfile) {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File project_dir = new File(fTmpDir, getName());
		
		assertTrue(project_dir.mkdirs());
		
		utils.copyBundleDirToFS(data_dir, project_dir);
		
		IProject p = TestUtils.createProject(getName(), project_dir);
		addProject(p);
		
		ISVDBIndexCache cache = fCacheFactory.createIndexCache(getName(), argfile);
		SVDBArgFileIndex2 index = new SVDBArgFileIndex2(getName(), 
				argfile, new SVDBWSFileSystemProvider(), cache, null);
	
		// Null builder so we control everything
		index.init(new NullProgressMonitor(), null);
	
		// Ensure the index is up-to-date
		index.loadIndex(new NullProgressMonitor());
		
		return index;
	}
	
}
