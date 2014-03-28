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


package net.sf.sveditor.core.tests.index.src_collection;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.old.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class SrcCollectionBasics extends SVCoreTestCaseBase {
	
	public void testFindSourceRecursePkg() {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testFindSourceRecursePkg");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/project_dir_src_collection_pkg/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		File path = new File(project_dir, "project_dir_src_collection_pkg");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = null; // index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1 = null;
		ISVDBItemBase class2 = null;
		ISVDBItemBase class3 = null;
		ISVDBItemBase def_function = null;
		List<ISVDBItemBase> markers = new ArrayList<ISVDBItemBase>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			String name = SVDBItem.getName(tmp_it);
			
			if (name.equals("class1")) {
				class1 = tmp_it;
			} else if (name.equals("class2")) {
				class2 = tmp_it;
			} else if (name.equals("class3")) {
				class3 = tmp_it;
			} else if (name.equals("def_function")) {
				def_function = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (ISVDBItemBase warn : markers) {
			log.debug("SVDBMarkerItem: " + 
					((SVDBMarker)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertNotNull("located def_function", def_function);
		assertEquals("class1", SVDBItem.getName(class1));
		
		// rgy.save_state();

		index.dispose();
		LogFactory.removeLogHandle(log);
	}
	
	public void testFindSourceRecurseNoPkg() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testFindSourceRecurseNoPkg");
		SVCorePlugin.getDefault().enableDebug(false);
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		utils.copyBundleDirToFS("/project_dir_src_collection_nopkg/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		File path = new File(project_dir, "project_dir_src_collection_nopkg");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				project_dir.getName(), path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = null; // index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1 = null;
		ISVDBItemBase class2 = null;
		ISVDBItemBase class3 = null;
		ISVDBItemBase def_function = null;
		ISVDBItemBase def_task = null;
		List<ISVDBItemBase> markers = new ArrayList<ISVDBItemBase>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			String name = SVDBItem.getName(tmp_it);
			
			log.debug("Item: " + tmp_it.getType() + " " + name);
			
			if (name.equals("class1")) {
				class1 = tmp_it;
			} else if (name.equals("class2")) {
				class2 = tmp_it;
			} else if (name.equals("class3")) {
				class3 = tmp_it;
			} else if (name.equals("def_function")) {
				def_function = tmp_it;
			} else if (name.equals("def_task")) {
				def_task = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (ISVDBItemBase warn : markers) {
			log.debug("SVDBMarkerItem: " + 
					((SVDBMarker)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertNotNull("located def_function", def_function);
		assertNotNull("located def_task", def_task);
		assertEquals("class1", SVDBItem.getName(class1));
		
		index.dispose();
		LogFactory.removeLogHandle(log);
	}

	/**
	 * Tests that module hierarchies are correctly compiled and
	 * defines from included files are located. Also ensures that
	 * `celldefine directives are processed properly
	 */
	public void testFindSourceRecurseModule() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testFindSourceRecurseModule");
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		utils.copyBundleDirToFS("/project_dir_src_collection_module/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		File path = new File(project_dir, "project_dir_src_collection_module");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				project_dir.getName(), path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = null; // index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase top=null, top_t=null, sub=null;
		ISVDBItemBase class1 = null;
		ISVDBItemBase class3 = null;
		ISVDBItemBase def_function = null;
		List<ISVDBItemBase> markers = new ArrayList<ISVDBItemBase>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			String name = SVDBItem.getName(tmp_it);
			
			log.debug("tmp_it: " + tmp_it.getType() + " " + name);
			
			if (name.equals("class1")) {
				class1 = tmp_it;
			} else if (name.equals("top")) {
				top = tmp_it;
			} else if (name.equals("top_t")) {
				top_t = tmp_it;
			} else if (name.equals("sub")) {
				sub = tmp_it;
			} else if (name.equals("class3")) {
				class3 = tmp_it;
			} else if (name.equals("def_function")) {
				def_function = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (ISVDBItemBase warn : markers) {
			log.debug("SVDBMarkerItem: " + 
					((SVDBMarker)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class3", class3);
		assertNotNull("located top", top);
		assertNotNull("located top_t", top_t);
		assertNotNull("located sub", sub);
		assertNotNull("located def_function", def_function);
		assertEquals("class1", SVDBItem.getName(class1));
		index.dispose();
		LogFactory.removeLogHandle(log);
	}

	/**
	 * Tests that module hierarchies are correctly compiled and
	 * defines from included files are located. Also ensures that
	 * `celldefine directives are processed properly
	 */
	public void testMissingIncludeRecurseModule() {
		LogHandle log = LogFactory.getLogHandle("testMissingIncludeRecurseModule");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		log.debug("--> testMissingIncludeRecurseModule()");
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		utils.copyBundleDirToFS("/project_dir_src_collection_module_missing_inc/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		File path = new File(project_dir, "project_dir_src_collection_module_missing_inc");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				project_dir.getName(), path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = null; // index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase top=null, top_t=null, sub=null;
		ISVDBItemBase class1 = null;
		ISVDBItemBase class3 = null;
		ISVDBItemBase def_function = null;
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			String name = SVDBItem.getName(tmp_it);
			
			log.debug("tmp_it: " + tmp_it.getType() + " " + name);
			
			if (name.equals("class1")) {
				class1 = tmp_it;
			} else if (name.equals("top")) {
				top = tmp_it;
			} else if (name.equals("top_t")) {
				top_t = tmp_it;
			} else if (name.equals("sub")) {
				sub = tmp_it;
			} else if (name.equals("class3")) {
				class3 = tmp_it;
			} else if (name.equals("def_function")) {
				def_function = tmp_it;
			}
		}
		
		ISVDBFileSystemProvider fs = index.getFileSystemProvider();
		String file_path = new File(path, "class1.svh").getAbsolutePath();
		/* SVDBFile file = */ index.parse(new NullProgressMonitor(), fs.openStream(file_path), file_path, null); 

		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		for (String file : index.getFileList(new NullProgressMonitor())) {
			List<SVDBMarker> tmp_m = index.getMarkers(file);
			markers.addAll(tmp_m);
		}

		for (ISVDBItemBase warn : markers) {
			log.debug("SVDBMarkerItem: " + ((SVDBMarker)warn).getMessage());
		}
		
		assertNotNull("located class1", class1);
		assertNotNull("located class3", class3);
		assertNotNull("located top", top);
		assertNotNull("located top_t", top_t);
		assertNotNull("located sub", sub);
		assertNotNull("located def_function", def_function);
		assertEquals("class1", SVDBItem.getName(class1));
		// Expect one marker -- missing_inc.svh
		assertEquals("Confirm 1 warnings", 1, markers.size());
		log.debug("<-- testMissingIncludeRecurseModule()");
		LogFactory.removeLogHandle(log);
	}

	public void testBasicClassIncludingModule() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testBasicClassIncludingModule");
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		utils.copyBundleDirToFS("/data/basic_module_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		File path = new File(project_dir, "basic_module_project");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				path.getName(), path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = null; // index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1 = null;
		ISVDBItemBase class2 = null;
		ISVDBItemBase class3 = null;
		List<ISVDBItemBase> markers = new ArrayList<ISVDBItemBase>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			String name = SVDBItem.getName(tmp_it);
			
			if (name.equals("class1")) {
				class1 = tmp_it;
			} else if (name.equals("class2")) {
				class2 = tmp_it;
			} else if (name.equals("class3")) {
				class3 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (ISVDBItemBase warn : markers) {
			log.debug("SVDBMarkerItem: " + 
					((SVDBMarker)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertEquals("class1", SVDBItem.getName(class1));
		index.dispose();
		LogFactory.removeLogHandle(log);
	}

	public void testBasicClassIncludingInterface() {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testBasicClassIncludingInterface");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		utils.copyBundleDirToFS("/data/basic_interface_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		File path = new File(project_dir, "basic_interface_project");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				path.getName(), path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = null; // index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1 = null;
		ISVDBItemBase class2 = null;
		ISVDBItemBase class3 = null;
		List<ISVDBItemBase> markers = new ArrayList<ISVDBItemBase>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			String name = SVDBItem.getName(tmp_it);
			
			if (name.equals("class1")) {
				class1 = tmp_it;
			} else if (name.equals("class2")) {
				class2 = tmp_it;
			} else if (name.equals("class3")) {
				class3 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (ISVDBItemBase warn : markers) {
			log.debug("SVDBMarkerItem: " + 
					((SVDBMarker)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertEquals("class1", SVDBItem.getName(class1));
		index.dispose();
		LogFactory.removeLogHandle(log);
	}

	public void testBasicClassIncludingProgram() {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testBasicClassIncludingProgram");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/basic_program_project/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		File path = new File(project_dir, "basic_program_project");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				path.getName(), path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = null; // index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1 = null;
		ISVDBItemBase class2 = null;
		ISVDBItemBase class3 = null;
		List<ISVDBItemBase> markers = new ArrayList<ISVDBItemBase>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			String name = SVDBItem.getName(tmp_it);
			
			if (name.equals("class1")) {
				class1 = tmp_it;
			} else if (name.equals("class2")) {
				class2 = tmp_it;
			} else if (name.equals("class3")) {
				class3 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (ISVDBItemBase warn : markers) {
			log.debug("SVDBMarkerItem: " + 
					((SVDBMarker)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertEquals("class1", SVDBItem.getName(class1));
		index.dispose();
		LogFactory.removeLogHandle(log);
	}

	public void testFSNewFileAdded() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testFSNewFileAdded");
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			TestUtils.delete(project_dir);
		}
		
		utils.copyBundleDirToFS("/project_dir_src_collection_module/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		File path = new File(project_dir, "project_dir_src_collection_module");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				project_dir.getName(), path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = null; // index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase top=null, top_t=null, sub=null;
		ISVDBItemBase class1 = null;
		ISVDBItemBase class3 = null;
		ISVDBItemBase def_function = null;
		List<ISVDBItemBase> markers = new ArrayList<ISVDBItemBase>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			String name = SVDBItem.getName(tmp_it);
			
			log.debug("tmp_it: " + tmp_it.getType() + " " + name);
			
			if (name.equals("class1")) {
				class1 = tmp_it;
			} else if (name.equals("top")) {
				top = tmp_it;
			} else if (name.equals("top_t")) {
				top_t = tmp_it;
			} else if (name.equals("sub")) {
				sub = tmp_it;
			} else if (name.equals("class3")) {
				class3 = tmp_it;
			} else if (name.equals("def_function")) {
				def_function = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (ISVDBItemBase warn : markers) {
			log.debug("SVDBMarkerItem: " + 
					((SVDBMarker)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class3", class3);
		assertNotNull("located top", top);
		assertNotNull("located top_t", top_t);
		assertNotNull("located sub", sub);
		assertNotNull("located def_function", def_function);
		assertEquals("class1", SVDBItem.getName(class1));
		
		// Now, create a new file
		PrintStream out = new PrintStream(new File(project_dir, "project_dir_src_collection_module/new_class.svh"));
		out.println("class new_class;");
		out.println("    int i;");
		out.println("endclass");
		out.close();
		
		// Now, try opening the new file
		String new_class_path = new File(project_dir, 
				"project_dir_src_collection_module/new_class.svh").getAbsolutePath();
		FileInputStream in = new FileInputStream(
				new File(project_dir, "project_dir_src_collection_module/new_class.svh"));				
		SVDBFile new_class_file = index.parse(new NullProgressMonitor(), in, new_class_path, null).second();
		
		assertNotNull(new_class_file);
		index.dispose();
		LogFactory.removeLogHandle(log);
	}

	/**
	 * Tests that relative include paths that extend above the workspace
	 * are correctly resolved
	 */
	public void testOutsideWsRelativeIncPaths() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		LogHandle log = LogFactory.getLogHandle("testOutsideWsRelativeIncPaths");
		log.debug("--> testOutsideWsRelativeIncPaths()");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File testdir = new File(fTmpDir, "testdir");
		File sub1 = new File(testdir, "sub1");
		File sub2 = new File(sub1, "sub2");
		File sub3 = new File(sub2, "sub3");
		
		if (sub2.exists()) {
			sub2.delete();
		}
		
		IProject project = TestUtils.createProject("a", new File(sub3, "a"));
		addProject(project);


		String data_dir = "/project_dir_src_collection_ws_ext_inc";
		utils.copyBundleFileToWS(data_dir + "/top.v", project);
		utils.copyBundleFileToFS(data_dir + "/xx.svh", sub3);
		utils.copyBundleFileToFS(data_dir + "/xxx.svh", sub2);
		utils.copyBundleFileToFS(data_dir + "/xxxx.svh", sub1);
		utils.copyBundleFileToFS(data_dir + "/xxxxx.svh", testdir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				project.getName(), "${workspace_loc}/a", 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.setGlobalDefine("TEST_MODE", "1");
		
		ISVDBItemIterator it = null; // index.getItemIterator(new NullProgressMonitor());
		while (it.hasNext()) {
			ISVDBItemBase it_t = it.nextItem();
			log.debug("it_t: " + it_t.getType() + " " + SVDBItem.getName(it_t));
		}
		
		IndexTestUtils.assertNoErrWarn(log, index);
		
		IndexTestUtils.assertFileHasElements(index, "top", "xx", "xxx", "xxxx", "xxxxx");
		
		ISVDBFileSystemProvider fs = index.getFileSystemProvider();
		String file_path = "${workspace_loc}/a/top.v";
		SVDBFile file = index.parse(new NullProgressMonitor(), fs.openStream(file_path), file_path, null).second();
		
		SVDBTestUtils.assertFileHasElements(file, "top");
		ISVDBItemBase top = SVDBTestUtils.findInFile(file, "top");

		assertNotNull("located top", top);
		
		// Expect one entry for missing include entry
		log.debug("<-- testOutsideWsRelativeIncPaths()");
		LogFactory.removeLogHandle(log);
	}

	public void testCapsExtensionFiles() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			project_dir.delete();
		}
		
		utils.copyBundleDirToFS("/data/caps_extension_files/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		File path = new File(project_dir, "caps_extension_files");
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				path.getName(), path.getAbsolutePath(), 
				SVDBSourceCollectionIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = null; // index.getItemIterator(new NullProgressMonitor());
		ISVDBItemBase class1 = null;
		ISVDBItemBase class2 = null;
		ISVDBItemBase class3 = null;
		List<ISVDBItemBase> markers = new ArrayList<ISVDBItemBase>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			String name = SVDBItem.getName(tmp_it);
			
			if (name.equals("class1")) {
				class1 = tmp_it;
			} else if (name.equals("class2")) {
				class2 = tmp_it;
			} else if (name.equals("class3")) {
				class3 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (ISVDBItemBase warn : markers) {
			System.out.println("SVDBMarkerItem: " + 
					((SVDBMarker)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertEquals("class1", SVDBItem.getName(class1));
		index.dispose();
	}

	public void testSrcCollectWinPathsNormalize() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testSrcCollectWinPathsNormalize");
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		File project_dir = new File(fTmpDir, "project_dir");
		
		if (project_dir.exists()) {
			TestUtils.delete(project_dir);
		}
		
		utils.copyBundleDirToFS("/data/index/src_collection_data/", project_dir);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		
		IProject project = TestUtils.createProject("project", project_dir);
		addProject(project);
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
				project_dir.getName(), 
				"${workspace_loc}\\project\\src_collection_data",
				SVDBSourceCollectionIndexFactory.TYPE, null);
	
		IndexTestUtils.assertFileHasElements(index, 
				"src_collection_data_pkg", "cls1", "cls2");
		index.dispose();
		LogFactory.removeLogHandle(log);
	}

}
