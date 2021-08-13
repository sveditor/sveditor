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
package org.eclipse.hdt.sveditor.ui.tests.editor;

import java.io.File;
import java.util.Map;

import org.eclipse.hdt.sveditor.core.tests.IndexTestUtils;
import org.eclipse.hdt.sveditor.core.tests.ProjectBuildMonitor;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IBuildConfiguration;
import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.hdt.sveditor.core.ISVProjectBuilderListener;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.builder.SVProjectBuilder;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexUtil;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;


public class TestIncrProjectChanges extends SVEditorTestCaseBase {
	
	public void testIncrParse() throws CoreException {
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<IProject, SVDBProjectData> pinfo = TestUtils.createSVEProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(pinfo.first());
		IProject p = pinfo.first();
		SVDBProjectData pdata = pinfo.second();
	
		ProjectBuildMonitor monitor = new ProjectBuildMonitor();
		pdata.addBuildListener(monitor);
			
		IFolder sub1 = TestUtils.mkdir(pinfo.first(), "sub1");
		TestUtils.copy(
				"class cls1;\n" +
				"	int a;\n" +
				"endclass\n",
				sub1.getFile(new Path("cls1.svh")));
		TestUtils.copy(
				"package pkg1;\n" +
				"	`include \"cls1.svh\"\n" + 
				"endpackage\n",
				sub1.getFile(new Path("pkg1.sv")));
		
		TestUtils.copy(
				"+incdir+./sub1\n" +
				"sub1/pkg1.sv\n",
				p.getFile(new Path("sve.f")));
		
		monitor.reset();
		SVProjectFileWrapper fw = pinfo.second().getProjectFileWrapper();
		fw.addArgFilePath("${project_loc}/sve.f");
		pinfo.second().setProjectFileWrapper(fw, true);
		
		assertTrue(monitor.wait(IncrementalProjectBuilder.FULL_BUILD, 10000));
		
		IndexTestUtils.assertFileHasElements(pdata.getProjectIndexMgr(), 
				"cls1", "pkg1");
		
		monitor.reset();
		
		TestUtils.mkdir(pinfo.first(), "sub2");
		TestUtils.copy(
				"class cls2;\n" +
				"	int a;\n" +
				"endclass\n",
				sub1.getFile(new Path("cls2.svh")));
		TestUtils.copy(
				"package pkg2;\n" +
				"	`include \"cls2.svh\"\n" + 
				"endpackage\n",
				sub1.getFile(new Path("pkg2.sv")));
		
		TestUtils.copy(
				"+incdir+./sub1\n" +
				"+incdir+./sub2\n" +
				"sub1/pkg1.sv\n" + 
				"sub1/pkg2.sv\n",
				p.getFile(new Path("sve.f")));
		
		assertTrue(monitor.wait(IncrementalProjectBuilder.AUTO_BUILD, 10000));
		
		IndexTestUtils.assertFileHasElements(pdata.getProjectIndexMgr(), 
				"cls1", "pkg1", "cls2", "pkg2");
	}

	public void testIncrParseRemoveFile() throws CoreException {
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<IProject, SVDBProjectData> pinfo = TestUtils.createSVEProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(pinfo.first());
		IProject p = pinfo.first();
		SVDBProjectData pdata = pinfo.second();
	
		ProjectBuildMonitor monitor = new ProjectBuildMonitor();
		pdata.addBuildListener(monitor);
			
		IFolder sub1 = TestUtils.mkdir(pinfo.first(), "sub1");
		TestUtils.copy(
				"class cls1;\n" +
				"	int a;\n" +
				"endclass\n",
				sub1.getFile(new Path("cls1.svh")));
		TestUtils.copy(
				"package pkg1;\n" +
				"	`include \"cls1.svh\"\n" + 
				"endpackage\n",
				sub1.getFile(new Path("pkg1.sv")));

		TestUtils.copy(
				"class cls2;\n" +
				"	int a;\n" +
				"endclass\n",
				sub1.getFile(new Path("cls2.svh")));
		TestUtils.copy(
				"package pkg2;\n" +
				"	`include \"cls2.svh\"\n" + 
				"endpackage\n",
				sub1.getFile(new Path("pkg2.sv")));
		
		TestUtils.copy(
				"+incdir+./sub1\n" +
				"+incdir+./sub2\n" +
				"sub1/pkg1.sv\n" + 
				"sub1/pkg2.sv\n",
				p.getFile(new Path("sve.f")));
		
		
		monitor.reset();
		SVProjectFileWrapper fw = pinfo.second().getProjectFileWrapper();
		fw.addArgFilePath("${project_loc}/sve.f");
		pinfo.second().setProjectFileWrapper(fw, true);
		
		assertTrue(monitor.wait(IncrementalProjectBuilder.FULL_BUILD, 10000));
		
		IndexTestUtils.assertFileHasElements(pdata.getProjectIndexMgr(), 
				"cls1", "pkg1", "cls2", "pkg2");
		
		TestUtils.copy(
				"+incdir+./sub1\n" +
				"sub1/pkg1.sv\n",
				p.getFile(new Path("sve.f")));
		
		monitor.reset();
		assertTrue(monitor.wait(IncrementalProjectBuilder.AUTO_BUILD, 10000));
		
		IndexTestUtils.assertFileHasElements(pdata.getProjectIndexMgr(), 
				"cls1", "pkg1");
		IndexTestUtils.assertDoesNotContain(pdata.getProjectIndexMgr(), 
				"cls2", "pkg2");
	}

	public void testIncrParseRemoveIncLevel1File() throws CoreException {
		SVCorePlugin.getDefault().enableDebug(false);
		Tuple<IProject, SVDBProjectData> pinfo = TestUtils.createSVEProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(pinfo.first());
		IProject p = pinfo.first();
		SVDBProjectData pdata = pinfo.second();
	
		ProjectBuildMonitor monitor = new ProjectBuildMonitor();
		pdata.addBuildListener(monitor);
			
		IFolder sub1 = TestUtils.mkdir(pinfo.first(), "sub1");
		TestUtils.copy(
				"class cls1;\n" +
				"	int a;\n" +
				"endclass\n",
				sub1.getFile(new Path("cls1.svh")));
		TestUtils.copy(
				"package pkg1;\n" +
				"	`include \"cls1.svh\"\n" + 
				"endpackage\n",
				sub1.getFile(new Path("pkg1.sv")));

		TestUtils.copy(
				"class cls2;\n" +
				"	int a;\n" +
				"endclass\n",
				sub1.getFile(new Path("cls2.svh")));
		TestUtils.copy(
				"package pkg2;\n" +
				"	`include \"cls2.svh\"\n" + 
				"endpackage\n",
				sub1.getFile(new Path("pkg2.sv")));
		
		TestUtils.copy(
				"+incdir+./sub1\n" +
				"+incdir+./sub2\n" +
				"sub1/pkg1.sv\n" + 
				"sub1/pkg2.sv\n",
				p.getFile(new Path("sve.f")));
		
		
		monitor.reset();
		SVProjectFileWrapper fw = pinfo.second().getProjectFileWrapper();
		fw.addArgFilePath("${project_loc}/sve.f");
		pinfo.second().setProjectFileWrapper(fw, true);
		
		assertTrue(monitor.wait(IncrementalProjectBuilder.FULL_BUILD, 10000));
		
		IndexTestUtils.assertFileHasElements(pdata.getProjectIndexMgr(), 
				"cls1", "pkg1", "cls2", "pkg2");
		
		TestUtils.copy(
				"+incdir+./sub1\n" +
				"sub1/pkg1.sv\n",
				p.getFile(new Path("sve.f")));
		
		monitor.reset();
		assertTrue(monitor.wait(IncrementalProjectBuilder.AUTO_BUILD, 10000));
		
		IndexTestUtils.assertFileHasElements(pdata.getProjectIndexMgr(), 
				"cls1", "pkg1");
		IndexTestUtils.assertDoesNotContain(pdata.getProjectIndexMgr(), 
				"cls2", "pkg2");
	}
}
