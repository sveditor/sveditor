/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.index.persistence;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

public class TestWorkspaceLibPersistence extends SVCoreTestCaseBase {
	
	/**
	 * Tests FileSystemLib persistence by changing a file, saving the database,
	 * and checking whether the changed timestamp is detected on reload
	 */
	public void disabled_testTimestampChangeDetected() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		IProject project_dir = TestUtils.createProject("project");
		addProject(project_dir);
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", project_dir);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_project/basic_lib.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.init(new NullProgressMonitor(), null);
		
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertFileHasElements(fLog, index, "class1");
		
		// Now, reset the registry
		reinitializeIndexRegistry();
		
		// Sleep to ensure that the timestamp is different
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}


		// Change class1.svh
		ByteArrayOutputStream out = utils.readBundleFile("/data/basic_lib_project/class1.svh");
		PrintStream ps = new PrintStream(out);
		
		ps.println("\n\n");
		ps.println("class class1_1;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, project_dir.getFile(new Path("basic_lib_project/class1.svh")));
		
		// Now, re-create the index
		index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/project/basic_lib_project/basic_lib.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.init(new NullProgressMonitor(), null);
		
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertFileHasElements(fLog, index, "class1_1");
	}

	/**
	 * Tests FileSystemLib persistence by changing a file, saving the database,
	 * and checking whether the changed timestamp is detected on reload
	 */
	public void disabled_testFilelistChangeDetected() {
		LogHandle log = LogFactory.getLogHandle("testFilelistChangeDetected");
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project_dir = TestUtils.createProject("project");
		addProject(project_dir);
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc/", project_dir);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_missing_inc/basic_lib_pkg.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.init(new NullProgressMonitor(), null);
		
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertFileHasElements(fLog, index, "class1");
		
		// Now, reset the registry
		reinitializeIndexRegistry();
		
		// Sleep to ensure that the timestamp is different
		log.debug("[NOTE] pre-sleep");
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		log.debug("[NOTE] post-sleep");

		// Change class1.svh
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		PrintStream ps = new PrintStream(out);
		
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, project_dir.getFile(new Path("basic_lib_missing_inc/class1_2.svh")));
		
		// Now, re-create the index
		index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/project/basic_lib_missing_inc/basic_lib_pkg.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.init(new NullProgressMonitor(), null);
		
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertFileHasElements(fLog, index, "class1_2");
	}

}
