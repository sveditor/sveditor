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

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.old.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

public class WSLibIndexFileChanges extends TestCase {
	
	private File				fTmpDir;
	private IProject			fProject;

	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
		fProject = null;
	}

	@Override
	protected void tearDown() throws Exception {
		SVCorePlugin.getDefault().getSVDBIndexRegistry().save_state();
		SVCorePlugin.getJobMgr().dispose();
		
		if (fProject != null) {
			TestUtils.deleteProject(fProject);
		}
		
		System.out.println("fTmpDir=" + fTmpDir);
		System.out.println("exists: " + fTmpDir.exists());
		
		if (fTmpDir != null && fTmpDir.exists()) {
			System.out.println("Deleting tmpdir");
			TestUtils.delete(fTmpDir);
		}
	}
	
	
	public void testMissingIncludeAdded() {
		SVCorePlugin.getDefault().enableDebug(false);
	
		int_testMissingIncludeAdded("testMissingIncludeAdded", fTmpDir);
	}
	
	private void int_testMissingIncludeAdded(String testname, File tmpdir) throws RuntimeException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(testname);
		
		fProject = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_missing_inc/", fProject);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(tmpdir));
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_missing_inc/basic_lib_pkg.sv", 
				SVDBLibPathIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1_it = null, class1_2_it = null;
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			log.debug("tmp_it: " + SVDBItem.getName(tmp_it));
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				class1_it = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class1_2")) {
				class1_2_it = tmp_it;
			}
		}
		
		assertNotNull("Expect to find class1", class1_it);
		assertNull("Expect to not find class1_2", class1_2_it);

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

		it = index.getItemIterator(new NullProgressMonitor());
		class1_it = null;
		class1_2_it = null;

		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			log.debug("tmp_it 2: " + SVDBItem.getName(tmp_it));
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				class1_it = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class1_2")) {
				class1_2_it = tmp_it;
			}
		}

		assertNotNull("Expect to find class1", class1_it);
		assertNotNull("Expect to find class1_2", class1_2_it);
//		index.dispose();
		LogFactory.removeLogHandle(log);
	}
}
