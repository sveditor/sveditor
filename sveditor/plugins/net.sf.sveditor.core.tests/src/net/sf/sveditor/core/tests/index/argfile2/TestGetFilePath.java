package net.sf.sveditor.core.tests.index.argfile2;

import java.io.File;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBFilePath;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex2;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestGetFilePath extends SVCoreTestCaseBase {
	
	public void testFindSVFilePath() {
		
		File project = new File(fTmpDir, "project");
		
		assertTrue(project.mkdirs());
	
		File argfile_f = new File(project, "argfile.f");
		TestUtils.copy(
				"root_pkg.sv",
				argfile_f);
		
		File root_pkg_sv = new File(project, "root_pkg.sv");
		TestUtils.copy(
				"package root_pkg;\n" +
				"	`include \"cls1.svh\"\n" +
				"endpackage\n",
				root_pkg_sv);
		
		File cls1_svh = new File(project, "cls1.svh");
		TestUtils.copy(
				"class cls1;\n" +
				"endclass\n",
				cls1_svh);
		
		IProject p = TestUtils.createProject("project", project);
		addProject(p);
		
		String argfile_f_path = "${workspace_loc}/project/argfile.f";
		String cls1_svh_path = "${workspace_loc}/project/cls1.svh";

		ISVDBIndexCache cache = fCacheFactory.createIndexCache(
				"GLOBAL", argfile_f_path);
		ISVDBIndex index = new SVDBArgFileIndex2("GLOBAL", 
				argfile_f_path,
				new SVDBWSFileSystemProvider(),
				cache, null);
		index.init(new NullProgressMonitor(), null);
	
		index.loadIndex(new NullProgressMonitor());
		
		List<SVDBFilePath> paths = index.getFilePath(cls1_svh_path);
		
		assertNotNull(paths);
		
		assertEquals(1, paths.size());
		
		SVDBFilePath path = paths.get(0);
		assertEquals(3, path.getPath().size());
		
	}

	public void testFindArgFilePath() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		File project = new File(fTmpDir, "project");
		
		assertTrue(project.mkdirs());
		
		File argfile_f = new File(project, "argfile.f");
		TestUtils.copy(
				"-f argfile_s1.f",
				argfile_f);
		
		File argfile_s1_f = new File(project, "argfile_s1.f");
		TestUtils.copy(
				"-f argfile_s2.f",
				argfile_s1_f);
		
		File argfile_s2_f = new File(project, "argfile_s2.f");
		TestUtils.copy(
				"root_pkg.sv",
				argfile_s2_f);
		
		File root_pkg_sv = new File(project, "root_pkg.sv");
		TestUtils.copy(
				"package root_pkg;\n" +
				"	`include \"cls1.svh\"\n" +
				"endpackage\n",
				root_pkg_sv);
		
		File cls1_svh = new File(project, "cls1.svh");
		TestUtils.copy(
				"class cls1;\n" +
				"endclass\n",
				cls1_svh);
		
		IProject p = TestUtils.createProject("project", project);
		addProject(p);
		
		String argfile_f_path = "${workspace_loc}/project/argfile.f";
		String argfile_s2_f_path = "${workspace_loc}/project/argfile_s2.f";

		ISVDBIndexCache cache = fCacheFactory.createIndexCache(
				"GLOBAL", argfile_f_path);
		ISVDBIndex index = new SVDBArgFileIndex2("GLOBAL", 
				argfile_f_path,
				new SVDBWSFileSystemProvider(),
				cache, null);
		index.init(new NullProgressMonitor(), null);
	
		index.loadIndex(new NullProgressMonitor());
		
		List<SVDBFilePath> paths = index.getFilePath(argfile_s2_f_path);
		
		assertNotNull(paths);
		
		assertEquals(1, paths.size());
		
		SVDBFilePath path = paths.get(0);
		assertEquals(3, path.getPath().size());
	
//		for (Tuple<SVDBFileTree, ISVDBItemBase> pi : path.getPath()) {
//			System.out.println("path: " + pi.first().getFilePath());
//		}
	}

}
