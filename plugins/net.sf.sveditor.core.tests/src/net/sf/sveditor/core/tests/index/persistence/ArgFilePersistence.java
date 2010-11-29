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


package net.sf.sveditor.core.tests.index.persistence;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBCoverGroup;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.db.SVDBParamPort;
import net.sf.sveditor.core.db.SVDBTaskFuncScope;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.SVDBDump;
import net.sf.sveditor.core.db.persistence.SVDBLoad;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.Path;

public class ArgFilePersistence extends TestCase 
	implements ISVDBIndexChangeListener {
	
	private File					fTmpDir;
	private int						fIndexRebuilt;

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		fTmpDir = TestUtils.createTempDir();
	}
	
	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		if (fTmpDir != null) {
			fTmpDir.delete();
			fTmpDir = null;
		}
	}
	
	public void testOVMXbusDirectDumpLoad() throws DBFormatException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testOVMXbusDirectDumpLoad");
		if (test_dir.exists()) {
			test_dir.delete();
		}
		test_dir.mkdirs();
		
		utils.unpackBundleZipToFS("/ovm.zip", test_dir);
		File xbus = new File(test_dir, "ovm/examples/xbus");
		
		/* IProject project_dir = */ TestUtils.createProject("xbus", xbus);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db);
		
		ISVDBIndex target_index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/xbus/examples/compile_questa_sv.f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		PersistenceIndex index = new PersistenceIndex(target_index);
		
		// Force loading
		ISVDBItemIterator<SVDBItem> item_it = index.getItemIterator();
		List<SVDBMarkerItem> errors = new ArrayList<SVDBMarkerItem>();
		
		while (item_it.hasNext()) {
			SVDBItem it = item_it.nextItem();
			if (it.getType() == SVDBItemType.Marker) {
				errors.add((SVDBMarkerItem)it);
			}
			assertNotNull("Item " + it.getName() + " has null location");
			if (it instanceof SVDBTaskFuncScope) {
				for (SVDBParamPort p : ((SVDBTaskFuncScope)it).getParams()) {
					assertNotNull("Parameter " + p.getName() + 
							" of " + it.getName() + " has null location",
							p.getLocation());
				}
			}
		}
		
		for (SVDBMarkerItem m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("Unexpected errors: ", 0, errors.size());
		
		SVDBDump dumper = new SVDBDump();
		
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		dumper.dump(index, out);

		SVDBLoad loader = new SVDBLoad();
		
		// May throw exception
		loader.load(index, new ByteArrayInputStream(out.toByteArray()));
		
		assertEquals(index.getDumpDBFileList().size(), index.getLoadDBFileList().size());
		
		for (int i=0; i<index.getDumpDBFileList().size(); i++) {
			SVDBFile fd = index.getDumpDBFileList().get(i);
			SVDBFile fl = index.getLoadDBFileList().get(i);
			
			SVDBItemTestComparator c = new SVDBItemTestComparator();
			c.compare(fd, fl);
		}
		
	}

	public void testWSArgFileTimestampChanged() {
		ByteArrayOutputStream 	out;
		PrintStream				ps;
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fTmpDir);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", 
				"${workspace_loc}/project/basic_lib_project/basic_lib.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem target_it = null;
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				target_it = tmp_it;
				break;
			}
		}

		assertNotNull("located class1", target_it);
		assertEquals("class1", target_it.getName());
		
		rgy.save_state();

		// Now, reset the registry
		rgy.init(fTmpDir);
		
		// Sleep to ensure that the timestamp is different
		System.out.println("[NOTE] pre-sleep");
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		System.out.println("[NOTE] post-sleep");

		// Change class1.svh
		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		ps.println("\n\n");
		ps.println("class class1_2;\n");
		ps.println("\n");
		ps.println("endclass\n\n");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, project_dir.getFile(new Path("basic_lib_project/class1_2.svh")));

		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		ps.println("basic_lib_pkg.sv");
		ps.println("class1_2.svh");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, project_dir.getFile(new Path("basic_lib_project/basic_lib.f")));

		// Now, re-create the index
		index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/project/basic_lib_project/basic_lib.f",
				SVDBArgFileIndexFactory.TYPE, null);
		it = index.getItemIterator();
		
		target_it = null;
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1_2")) {
				target_it = tmp_it;
				break;
			}
		}
		
		assertNotNull("located class1_2", target_it);
		assertEquals("class1_2", target_it.getName());
	}

	public void testWSArgFileTimestampUnchanged() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		IProject project_dir = TestUtils.createProject("project");
		
		utils.copyBundleDirToWS("/data/basic_lib_project/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fTmpDir);
		
		fIndexRebuilt = 0;
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", 
				"${workspace_loc}/project/basic_lib_project/basic_lib.f", 
				SVDBArgFileIndexFactory.TYPE, null);
		index.addChangeListener(this);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBModIfcClassDecl target_it = null, target_orig = null;
		List<SVDBItem> orig_list = new ArrayList<SVDBItem>();
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				target_it = (SVDBModIfcClassDecl)tmp_it;
				target_orig = (SVDBModIfcClassDecl)tmp_it.duplicate();
			}
			orig_list.add(tmp_it.duplicate());
			if (tmp_it.getType() == SVDBItemType.Covergroup) {
				SVDBCoverGroup cg = (SVDBCoverGroup)tmp_it;
				SVDBCoverGroup cg2 = (SVDBCoverGroup)cg.duplicate();
				assertEquals(cg, cg2);
			}
		}

		for (int i=0; i<orig_list.size(); i++) {
			if ((orig_list.get(i) instanceof ISVDBScopeItem) &&
					orig_list.get(i).getType() != SVDBItemType.File) {
				assertTrue("Item " + orig_list.get(i).getType() + " " + orig_list.get(i).getName() + 
						" Not Equal " + orig_list.get(i).getType() + " " + orig_list.get(i).getName(),
						orig_list.get(i).equals(orig_list.get(i)));
			}
		}

		assertEquals("Index not initially rebuilt", 1, fIndexRebuilt);
		assertNotNull("located class1", target_it);
		assertEquals("class1", target_it.getName());
		
		rgy.save_state();

		// Now, reset the registry
		rgy.init(fTmpDir);
		
		// Sleep to ensure that the timestamp is different
		System.out.println("[NOTE] pre-sleep");
		try {
			Thread.sleep(2000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		System.out.println("[NOTE] post-sleep");


		fIndexRebuilt = 0;
		// Now, re-create the index
		index = rgy.findCreateIndex("GENERIC",
				"${workspace_loc}/project/basic_lib_project/basic_lib.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.addChangeListener(this);
		it = index.getItemIterator();
		
		target_it = null;
		List<SVDBItem> new_list = new ArrayList<SVDBItem>();
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			new_list.add(tmp_it);
			
			if (tmp_it.getName().equals("class1")) {
				target_it = (SVDBModIfcClassDecl)tmp_it;
			}
		}
		
		target_it.equals(target_orig);
		
		assertEquals("item count changed", orig_list.size(), new_list.size());
		// Compare individual items first
		for (int i=0; i<orig_list.size(); i++) {
			if (!(orig_list.get(i) instanceof ISVDBScopeItem)) {
				assertTrue("Item " + orig_list.get(i).getType() + " " + orig_list.get(i).getName() + 
						" Not Equal " + new_list.get(i).getType() + " " + new_list.get(i).getName(),
						orig_list.get(i).equals(new_list.get(i)));
			}
		}

		// Compare non-file scopes next
		for (int i=0; i<orig_list.size(); i++) {
			if ((orig_list.get(i) instanceof ISVDBScopeItem) &&
					orig_list.get(i).getType() != SVDBItemType.File &&
					orig_list.get(i).getType() != SVDBItemType.Class) {
				if (orig_list.get(i).getType() == SVDBItemType.Function &&
						orig_list.get(i).getName().equals("new")) {
					SVDBTaskFuncScope f1 = (SVDBTaskFuncScope)orig_list.get(i);
					SVDBTaskFuncScope f2 = (SVDBTaskFuncScope)new_list.get(i);
					f1.equals(f2);
				} else {
					assertTrue("Item " + orig_list.get(i).getType() + " " + orig_list.get(i).getName() + 
							" Not Equal " + new_list.get(i).getType() + " " + new_list.get(i).getName(),
							orig_list.get(i).equals(new_list.get(i)));
				}
			}
		}

		// Compare everything next
		for (int i=0; i<orig_list.size(); i++) {
			if (orig_list.get(i).getType() == SVDBItemType.File &&
					orig_list.get(i).getName().equals("class1.svh")) {
				SVDBFile c1 = (SVDBFile)orig_list.get(i);
				SVDBFile c2 = (SVDBFile)new_list.get(i);
				
				c1.equals(c2);
			}
			assertTrue("Item " + orig_list.get(i).getType() + " " + orig_list.get(i).getName() + 
					" Not Equal " + new_list.get(i).getType() + " " + new_list.get(i).getName(),
					orig_list.get(i).equals(new_list.get(i)));
		}

		assertEquals("Index rebuilt without cause", 0, fIndexRebuilt);
		assertNotNull("located class1", target_it);
		assertEquals("class1", target_it.getName());
	}

	public void testFSArgFileTimestampChanged() {
		ByteArrayOutputStream out;
		PrintStream ps;
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_lib_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(project_dir);
		
		File path = new File(project_dir, "basic_lib_project/basic_lib.f");
		ISVDBIndex index = rgy.findCreateIndex("GENERIC", path.getAbsolutePath(), 
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem target_it = null;
		SVDBItem class1_2 = null;
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				target_it = tmp_it;
			} else if (tmp_it.getName().equals("class1_2")) {
				class1_2 = tmp_it;
			}
		}

		assertNotNull("located class1", target_it);
		assertEquals("class1", target_it.getName());
		assertNull("Ensure don't fine class1_2 yet", class1_2);
		
		rgy.save_state();

		System.out.println("** RESET **");
		// Now, reset the registry
		rgy.init(project_dir);
		
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
		System.out.println("** Create class1_2.svh **");
		TestUtils.copy(out, new File(project_dir, "basic_lib_project/class1_2.svh"));

		out = new ByteArrayOutputStream();
		ps = new PrintStream(out);
		ps.println("basic_lib_pkg.sv");
		ps.println("class1_2.svh");
		ps.flush();
		
		// Now, write back the file
		TestUtils.copy(out, new File(project_dir, "basic_lib_project/basic_lib.f"));

		// Now, re-create the index
		index = rgy.findCreateIndex("GENERIC", path.getAbsolutePath(), 
				SVDBArgFileIndexFactory.TYPE, null);
		it = index.getItemIterator();
		
		target_it = null;
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1_2")) {
				target_it = tmp_it;
				break;
			}
		}
		
		assertNotNull("located class1_2", target_it);
		assertEquals("class1_2", target_it.getName());
	}

	public void index_changed(int reason, SVDBFile file) {}

	public void index_rebuilt() {
		fIndexRebuilt++;
	}
	
}
