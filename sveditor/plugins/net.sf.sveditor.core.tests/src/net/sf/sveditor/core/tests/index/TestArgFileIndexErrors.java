/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.tests.index;

import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;

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
		
		boolean build_ok = pmgr.rebuildProject(new NullProgressMonitor(), project_dir, true, null);
		
		assertTrue(build_ok);
		
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
