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


package org.sveditor.core.tests.index.libIndex;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;

import org.sveditor.core.tests.IndexTestUtils;
import org.sveditor.core.tests.SVCoreTestCaseBase;
import org.sveditor.core.tests.SVCoreTestsPlugin;
import org.sveditor.core.tests.utils.BundleUtils;
import org.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;

public class WSArgFileIndexChanges extends SVCoreTestCaseBase {
	
	public void disabled_testArgFileChange() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		int_testArgFileChange(fTmpDir);
	}
	
	private void int_testArgFileChange(File tmpdir) {
		System.out.println("Begin int_testArgFileChange");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject p = TestUtils.createProject("project");
		addProject(p);
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", p);
		
		reinitializeIndexRegistry();
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_project/basic_lib.f", 
				SVDBArgFileIndexFactory.TYPE, null);
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
		TestUtils.copy(out, p.getFile(new Path("basic_lib_project/class1_2.svh")));

		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		
		ps.println("\n\n");
		ps.println("basic_lib_pkg.sv");
		ps.println("class1_2.svh");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, p.getFile(new Path("basic_lib_project/basic_lib.f")));
	
		System.out.println("--> Sleep");
		try {
			Thread.sleep(1000);
		} catch (InterruptedException e) {}
		System.out.println("<-- Sleep");
		
		index.loadIndex(new NullProgressMonitor());

		IndexTestUtils.assertFileHasElements(fLog, index, "class1");
		IndexTestUtils.assertFileHasElements(fLog, index, "class1_2");

		index.dispose();
	}

}
