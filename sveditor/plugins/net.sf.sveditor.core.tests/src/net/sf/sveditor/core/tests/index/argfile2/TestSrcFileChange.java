package net.sf.sveditor.core.tests.index.argfile2;

import java.io.File;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Path;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.tests.index.IndexTests;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestSrcFileChange extends TestFileChangeBase {

	public void testRootFileChanged() {
		SVCorePlugin.getDefault().enableDebug(true);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertDoesNotContain(
				pd.getProjectIndexMgr(), "my_cls");

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"	class my_cls;\n" +
				"	endclass\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_cls", SVDBItemType.ClassDecl);
	}
	
	public void testIncludedFileChanged() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"package my_pkg;\n" +
				"	`include \"my_file1.svh\"\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		
		SVFileUtils.copy(
				"class c1;\n" +
				"endclass\n",
				p.getFile(new Path("my_file1.svh"))
				);
		
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"c1", SVDBItemType.ClassDecl);

		SVFileUtils.copy(
				"class c2;\n" +
				"endclass\n",
				p.getFile(new Path("my_file1.svh"))
				);
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"c2", SVDBItemType.ClassDecl);
		IndexTests.assertDoesNotContain(pd.getProjectIndexMgr(), 
				"c1");
	}
	
	public void testIncludedFileAdded() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"package my_pkg;\n" +
				"	`include \"my_file1.svh\"\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		
		SVFileUtils.copy(
				"class c1;\n" +
				"endclass\n",
				p.getFile(new Path("my_file1.svh"))
				);
		SVFileUtils.copy(
				"class c2;\n" +
				"endclass\n",
				p.getFile(new Path("my_file2.svh"))
				);
		
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"c1", SVDBItemType.ClassDecl);
		IndexTests.assertDoesNotContain(pd.getProjectIndexMgr(), 
				"c2");

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"	`include \"my_file1.svh\"\n" +
				"	`include \"my_file2.svh\"\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"c1", SVDBItemType.ClassDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"c2", SVDBItemType.ClassDecl);
	}

	public void testMissingIncludeFileAdded() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"package my_pkg;\n" +
				"	`include \"my_file1.svh\"\n" +
				"	`include \"my_file2.svh\"\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		
		SVFileUtils.copy(
				"class c1;\n" +
				"endclass\n",
				p.getFile(new Path("my_file1.svh"))
				);
		
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"c1", SVDBItemType.ClassDecl);
		IndexTests.assertDoesNotContain(pd.getProjectIndexMgr(), 
				"c2");

		SVFileUtils.copy(
				"class c2;\n" +
				"endclass\n",
				p.getFile(new Path("my_file2.svh"))
				);
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"c1", SVDBItemType.ClassDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"c2", SVDBItemType.ClassDecl);
	}
	
	public void testIncludedFileRemoved() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"package my_pkg;\n" +
				"	`include \"my_file1.svh\"\n" +
				"	`include \"my_file2.svh\"\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		
		SVFileUtils.copy(
				"class c1;\n" +
				"endclass\n",
				p.getFile(new Path("my_file1.svh"))
				);
		SVFileUtils.copy(
				"class c2;\n" +
				"endclass\n",
				p.getFile(new Path("my_file2.svh"))
				);
		
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"c1", SVDBItemType.ClassDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"c2", SVDBItemType.ClassDecl);

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"	`include \"my_file1.svh\"\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"c1", SVDBItemType.ClassDecl);
		IndexTests.assertDoesNotContain(pd.getProjectIndexMgr(), 
				"c2");
	}
	
}
