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
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;

public class WSArgFileIndexChanges extends TestCase {
	
	@Override
	protected void tearDown() throws Exception {
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.save_state();
	}

	public void testArgFileChange() {
		File tmpdir = TestUtils.createTempDir();
		SVCorePlugin.getDefault().enableDebug(false);
		
		try {
			int_testArgFileChange(tmpdir);
		} catch (RuntimeException e) {
			throw e;
		} finally {
			TestUtils.delete(tmpdir);
		}
	}
	
	private void int_testArgFileChange(File tmpdir) {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		final IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", project_dir);
		
		File db = new File(tmpdir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(tmpdir));
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC", 
				"${workspace_loc}/project/basic_lib_project/basic_lib.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1_it = null, class1_2_it = null;
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				class1_it = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class1_2")) {
				class1_2_it = tmp_it;
			}
		}
		
		assertNotNull("Expect to find class1", class1_it);
		assertNull("Expect to not fine class1_2", class1_2_it);


		// Wait a bit...
		/*
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) { }
		 */

		ByteArrayOutputStream out = new ByteArrayOutputStream();
		PrintStream ps = new PrintStream(out);
		
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, project_dir.getFile(new Path("basic_lib_project/class1_2.svh")));

		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		
		ps.println("\n\n");
		ps.println("basic_lib_pkg.sv");
		ps.println("class1_2.svh");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, project_dir.getFile(new Path("basic_lib_project/basic_lib.f")));

		it = index.getItemIterator(new NullProgressMonitor());
		class1_it = null;
		class1_2_it = null;

		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (SVDBItem.getName(tmp_it).equals("class1")) {
				class1_it = tmp_it;
			} else if (SVDBItem.getName(tmp_it).equals("class1_2")) {
				class1_2_it = tmp_it;
			}
		}

		assertNotNull("Expect to find class1", class1_it);
		assertNotNull("Expect to find class1_2", class1_2_it);
		index.dispose();
	}

}
