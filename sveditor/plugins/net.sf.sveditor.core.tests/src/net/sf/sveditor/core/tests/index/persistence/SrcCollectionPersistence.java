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
import java.io.File;
import java.io.PrintStream;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.old.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

public class SrcCollectionPersistence extends SVCoreTestCaseBase implements ISVDBIndexChangeListener {
	
	private IProject				fProject;
	private int						fIndexRebuildCnt;

	public void testWSTimestampChanged() {
		ByteArrayOutputStream 	out;
		PrintStream				ps;
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		fIndexRebuildCnt = 0;
		
		fProject = TestUtils.createProject("project");
		addProject(fProject);
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", fProject);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", "${workspace_loc}/project/basic_lib_project", 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		
		IndexTestUtils.assertFileHasElements(fLog, index, "class1");
		
		rgy.close();

		// Now, reset the registry
		rgy.init(fCacheFactory);
		
		// Sleep to ensure that the timestamp is different
		fLog.debug("[NOTE] pre-sleep");
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		fLog.debug("[NOTE] post-sleep");

		// Change class1.svh
		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, fProject.getFile(new Path("basic_lib_project/class1_2.svh")));

		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/project/basic_lib_project",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.loadIndex(new NullProgressMonitor());
		
		index.addChangeListener(this);
		
		assertEquals("index not rebuilt", 1, fIndexRebuildCnt);
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, "class1_2");
	}

	public void disabled_testWSNoChange() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		fProject = TestUtils.createProject("project");
		addProject(fProject);
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", fProject);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", "${workspace_loc}/project/basic_lib_project", 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, "class1");

		rgy.close();

		fLog.debug("[NOTE] pre-sleep");
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		fLog.debug("[NOTE] post-sleep");

		// Now, reset the registry
		rgy.init(fCacheFactory);

		fIndexRebuildCnt = 0;

		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(), 
				"GENERIC", "${workspace_loc}/project/basic_lib_project",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		index.loadIndex(new NullProgressMonitor());
		
		assertEquals("index rebuilt", 0, fIndexRebuildCnt);
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, "class1");
	}

	public void disabled_testFSTimestampChanged() {
		ByteArrayOutputStream out;
		PrintStream ps;
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		fIndexRebuildCnt = 0;
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		utils.copyBundleDirToFS("/data/basic_lib_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		File path = new File(project_dir, "basic_lib_project");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, "class1");
		IndexTestUtils.assertDoesNotContain(index, "class1_2");
		
		rgy.close();

		fLog.debug("** RESET **");
		// Now, reset the registry
		rgy.init(fCacheFactory);
		
		// Sleep to ensure that the timestamp is different
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		// Change class1.svh
		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		fLog.debug("** Create class1_2.svh **");
		TestUtils.copy(out, new File(project_dir, "basic_lib_project/class1_2.svh"));

		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, 
				"class1", "class1_2");
	}

	public void disabled_testFSNoChange() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		fIndexRebuildCnt = 0;
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_lib_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
		
		File path = new File(project_dir, "basic_lib_project");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertFileHasElements(index, "class1");
		IndexTestUtils.assertDoesNotContain(index, "class1_2");
		
		rgy.close();

		fLog.debug("** RESET **");
		// Now, reset the registry
		rgy.init(fCacheFactory);
		
		// Sleep to ensure that the timestamp is different
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		
		fIndexRebuildCnt = 0;

		// Now, re-create the index
		index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		index.loadIndex(new NullProgressMonitor());
		
		assertEquals("index rebuilt", 0, fIndexRebuildCnt);
		IndexTestUtils.assertFileHasElements(index, "class1");
	}

	public void index_changed(int reason, SVDBFile file) {}

	public void index_rebuilt() {
		fIndexRebuildCnt++;
	}
	
}
