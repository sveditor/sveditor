package net.sf.sveditor.core.tests.index;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestArgFileIndexErrors extends SVCoreTestCaseBase {

	public void testErrorMarkersRemovedAfterCleanRebuild_1() throws CoreException {
		String testname = getName();
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject(testname);
		addProject(project_dir);
		
		
		IFile file1_f = project_dir.getFile("file1.f");
		TestUtils.copy(
				"test_pkg.sv\n",
				file1_f);

		IFile test_pkg_sv = project_dir.getFile("test_pkg.sv");
		TestUtils.copy(
				"package test_pkg;\n" +
				"	`MISSING_MACRO\n" +
				"	class cls1;\n" +
				"	endclass\n" +
				"endpackage\n",
				test_pkg_sv);
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(project_dir);
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		fw.addArgFilePath("${workspace_loc}/" + testname + "/file1.f");
		pdata.setProjectFileWrapper(fw);
		
		pmgr.rebuildProject(new NullProgressMonitor(), project_dir, true);
		
		IMarker markers[] = project_dir.findMarkers(IMarker.PROBLEM, true, LEVEL_MAX);
		
		assertEquals(1, markers.length);
		
		TestUtils.copy(
				"package test_pkg;\n" +
				"	class cls1;\n" +
				"	endclass\n" +
				"endpackage\n",
				test_pkg_sv);
		
		pmgr.rebuildProject(new NullProgressMonitor(), project_dir, true);
		markers = project_dir.findMarkers(IMarker.PROBLEM, true, LEVEL_MAX);
		assertEquals(0, markers.length);
	}

	public void testErrorMarkersRemovedAfterCleanRebuild_2() throws CoreException {
		String testname = getName();
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		final IProject project_dir = TestUtils.createProject(testname);
		addProject(project_dir);

		IFolder sub = TestUtils.mkdir(project_dir, "sub");
		
		IFile inc_svh_f = sub.getFile("inc.svh");
		TestUtils.copy(
				"`define MISSING_MACRO\n",
				inc_svh_f);
		
		IFile file1_f = project_dir.getFile("file1.f");
		TestUtils.copy(
				"test_pkg.sv\n",
				file1_f);

		IFile test_pkg_sv = project_dir.getFile("test_pkg.sv");
		TestUtils.copy(
				"`include \"inc.svh\"\n" +
				"package test_pkg;\n" +
				"	`MISSING_MACRO\n" +
				"	class cls1;\n" +
				"	endclass\n" +
				"endpackage\n",
				test_pkg_sv);
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pdata = pmgr.getProjectData(project_dir);
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		fw.addArgFilePath("${workspace_loc}/" + testname + "/file1.f");
		pdata.setProjectFileWrapper(fw);
		
		pmgr.rebuildProject(new NullProgressMonitor(), project_dir, true);
		
		IMarker markers[] = project_dir.findMarkers(IMarker.PROBLEM, true, LEVEL_MAX);
		
		assertEquals(2, markers.length);
		
		TestUtils.copy(
				"+incdir+./sub\n" +
				"test_pkg.sv\n",
				file1_f);
		
		pmgr.rebuildProject(new NullProgressMonitor(), project_dir, true);
		markers = project_dir.findMarkers(IMarker.PROBLEM, true, LEVEL_MAX);
		assertEquals(0, markers.length);
	}
}
