/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.index.libIndex;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.old.SVDBLibPathIndexFactory;
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

public class WSLibIndexFileChanges extends SVCoreTestCaseBase {
	
	private IProject			fProject;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fTmpDir = TestUtils.createTempDir();
		fProject = null;
	}

	@Override
	protected void tearDown() throws Exception {
		SVCorePlugin.getDefault().getSVDBIndexRegistry().close();
		SVCorePlugin.getJobMgr().dispose();
		
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
		}
		
		System.out.println("fTmpDir=" + fTmpDir);
		System.out.println("exists: " + fTmpDir.exists());
	
		super.tearDown();
	}
	
	
	public void disabled_testMissingIncludeAdded() {
		SVCorePlugin.getDefault().enableDebug(false);
	
		int_testMissingIncludeAdded("testMissingIncludeAdded", fTmpDir);
	}
	
	private void int_testMissingIncludeAdded(String testname, File tmpdir) throws RuntimeException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(testname);
		
		fProject = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc/", fProject);
		
		SVDBIndexRegistry rgy = fIndexRgy;
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_missing_inc/basic_lib_pkg.sv", 
				SVDBLibPathIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));

		IndexTestUtils.assertFileHasElements(fLog, index, "class1");
		IndexTestUtils.assertDoesNotContain(index, "class1_2");

		ByteArrayOutputStream out = new ByteArrayOutputStream();
		PrintStream ps = new PrintStream(out);
		
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, fProject.getFile(new Path("basic_lib_missing_inc/class1_2.svh")));

		log.debug(">> SLEEP");
		// Wait a bit...
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) { }
		log.debug("<< SLEEP");
		
		index.loadIndex(new NullProgressMonitor());

		IndexTestUtils.assertFileHasElements(fLog, index, "class1", "class1_2");

		LogFactory.removeLogHandle(log);
	}
}
