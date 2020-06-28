/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.index.libIndex;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;

import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.eclipse.hdt.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class WSLibIndexFileChanges extends SVCoreTestCaseBase {
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
	}

	@Override
	protected void tearDown() throws Exception {
		SVCorePlugin.getDefault().getSVDBIndexRegistry().close();
		SVCorePlugin.getJobMgr().dispose();
		
		super.tearDown();
	}
	
	
	public void disabled_testMissingIncludeAdded() {
		SVCorePlugin.getDefault().enableDebug(false);
	
		int_testMissingIncludeAdded("testMissingIncludeAdded", fTmpDir);
	}
	
	private void int_testMissingIncludeAdded(String testname, File tmpdir) throws RuntimeException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(testname);
		
		IProject project = TestUtils.createProject("project");
		addProject(project);
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc/", project);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_missing_inc/basic_lib_pkg.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		
		index.init(new NullProgressMonitor(), null);
		
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
		TestUtils.copy(out, project.getFile(new Path("basic_lib_missing_inc/class1_2.svh")));

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
