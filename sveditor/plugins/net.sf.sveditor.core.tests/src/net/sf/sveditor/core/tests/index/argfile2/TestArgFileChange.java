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

public class TestArgFileChange extends TestFileChangeBase {

	public void testRootFileAdd_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
	}

	public void testRootFileChangeSrcFile_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
	
		// Rewrite the root file so it contains my_pkg2 rather than my_pkg
		SVFileUtils.copy(
				"package my_pkg2;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		
		assertTrue(waitIndexEvent());
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg2", SVDBItemType.PackageDecl);
		IndexTests.assertDoesNotContain(pd.getProjectIndexMgr(), "my_pkg");
	}

	public void testRootFileRemoveSrcFile_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv")));
		
		SVFileUtils.copy(
				"package my_pkg2;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg2.sv")));
		
		SVFileUtils.copy(
				"./my_pkg.sv\n" + 
				"./my_pkg2.sv\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg2", SVDBItemType.PackageDecl);
	
		// Rewrite the sve.f so it doesn't contain my_pkg2
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));

		assertTrue(waitIndexEvent());
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertDoesNotContain(pd.getProjectIndexMgr(), "my_pkg2");
	}

	public void testRootFileRemoveSrcFileLeaveRef_1() {
		SVCorePlugin.getDefault().enableDebug(true);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv")));
		
		SVFileUtils.copy(
				"package my_pkg2;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg2.sv")));
		
		SVFileUtils.copy(
				"./my_pkg.sv\n" + 
				"./my_pkg2.sv\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg2", SVDBItemType.PackageDecl);

		// Delete my_pkg2.sv
		SVFileUtils.delete(p.getFile(new Path("my_pkg2.sv")));
	
		fLog.debug("--> Wait for second rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for second rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertDoesNotContain(pd.getProjectIndexMgr(), "my_pkg2");
	}

	public void testRootFileRemoveFileListLeaveRef_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		fLog.debug("--> Wait for rebuild event (1)");
		addIndex(pd.getProjectIndexMgr());
		fLog.debug("<-- Wait for rebuild event (1)");

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv")));
		
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("my_pkg.f")));
		
		SVFileUtils.copy(
				"package my_pkg2;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg2.sv")));
		
		SVFileUtils.copy(
				"./my_pkg2.sv\n",
				p.getFile(new Path("my_pkg2.f")));
		
		SVFileUtils.copy(
				"-f ./my_pkg.f\n" + 
				"-f ./my_pkg2.f\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event (2)");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event (2)");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg2", SVDBItemType.PackageDecl);

		// Delete my_pkg2.sv
		SVFileUtils.delete(p.getFile(new Path("my_pkg2.f")));
	
		fLog.debug("--> Wait for rebuild event (3)");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event (3)");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertDoesNotContain(pd.getProjectIndexMgr(), "my_pkg2");
	}
	
	public void testRootFileChangeIncSrcFile_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");
		
		SVFileUtils.copy(
				"\n",
				p.getFile(new Path("my_cls.svh"))
				);

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"`include \"my_cls.svh\"\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertDoesNotContain(
				pd.getProjectIndexMgr(), "my_cls");
	
		// Rewrite the included file so it does declare a class
		SVFileUtils.copy(
				"class my_cls;\n" +
				"endclass\n",
				p.getFile(new Path("my_cls.svh"))
				);
		
		fLog.debug("--> Wait for update event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for update event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_cls", SVDBItemType.ClassDecl);
	}
	
	public void testRootFileChangeFileList_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("my_pkg.f")));
		
		SVFileUtils.copy(
				"-f ./my_pkg.f\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
	}	

}
