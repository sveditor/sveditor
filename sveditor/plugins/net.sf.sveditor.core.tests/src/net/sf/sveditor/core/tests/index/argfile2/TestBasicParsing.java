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
package net.sf.sveditor.core.tests.index.argfile2;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Set;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.builder.SVDBIndexBuilder;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileIndexCache;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystem;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystemDataInput;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystemDataOutput;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceRW;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;

public class TestBasicParsing extends SVCoreTestCaseBase {
	private ISVDBIndexCacheMgr				fPrvCacheMgr;
	

	@Override
	protected void setUp() throws Exception {
		super.setUp();
		File db2 = new File(fTmpDir, "db2");
		assertTrue(db2.mkdirs());
		fPrvCacheMgr = SVCorePlugin.createCacheMgr(db2);
	
		SVCorePlugin.getDefault().getSVDBIndexRegistry().init(fPrvCacheMgr);
	}

	@Override
	protected void tearDown() throws Exception {
//		fPrvCacheMgr.dispose();
		super.tearDown();
	}

	public void testParseUVM() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().setTestDebugLevel(0);
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		TestUtils.copy(
				"+incdir+uvm/src\n" +
				"uvm/src/uvm_pkg.sv",
				new File(fTmpDir, "uvm.f"));
		
		String base_location = new File(fTmpDir, "uvm.f").getAbsolutePath();
		
		SVDBArgFileIndex index = new SVDBArgFileIndex(
				getName(), base_location,
				new SVDBWSFileSystemProvider(),
				fPrvCacheMgr.createIndexCache(getName(), base_location),
				null);
		
		long start, end;
		
		start = System.currentTimeMillis();
		index.init(new NullProgressMonitor(), SVCorePlugin.getDefault().getIndexBuilder());
		index.loadIndex(new NullProgressMonitor());
		end = System.currentTimeMillis();
		System.out.println("Parse UVM in " + (end-start) + "ms");
		
		SVDBFileIndexCache cache = (SVDBFileIndexCache)index.getCache();
		
		IDBWriter writer = new SVDBPersistenceRW();
		IDBReader reader = new SVDBPersistenceRW();
		
		Set<String> files = cache.getFileList(false);
		SVDBFile file = cache.getFile(new NullProgressMonitor(), files.iterator().next());
	
		File db3 = new File(fTmpDir, "db3");
		SVDBFileSystem fs = new SVDBFileSystem(db3, SVCorePlugin.getVersion());
		try {
			fs.init();
			
			SVDBFileSystemDataOutput dout = new SVDBFileSystemDataOutput();
			SVDBFileSystemDataInput  din;
			
			writer.init(dout);
			
			writer.writeObject(SVDBFile.class, file);
			
			int fileid = fs.writeFile("dout", dout);
			
			din = fs.readFile("dout", fileid);
			
//			din.fDebugEn = true;
		
			int len = dout.getLength();
			List<byte[]> din_pages = din.getPages();
			List<byte[]> dout_pages = dout.getPages();
			int dout_idx=0;
			int din_idx=din.getPageIdx();
			int din_page_idx=din.getPagesIdx();
			int dout_page_idx=0;
	
			System.out.println("init: din_page_idx=" + din_page_idx);
			System.out.println("init: din_idx=" + din_idx);
			System.out.println("init: dout_page_idx=" + dout_page_idx);
			System.out.println("init: dout_idx=" + dout_idx);
			
			for (int i=0; i<len; i++) {
				int din_val  = din_pages.get(din_page_idx)[din_idx];
				int dout_val = dout_pages.get(dout_page_idx)[dout_idx];
				
//				System.out.println("din_val=" + din_val + " dout_val=" + dout_val);
				
				if (din_val != dout_val) {
					System.out.println("[ERROR] @ " + din_page_idx + ":" + din_idx +
							" " + dout_page_idx + ":" + dout_idx);
					System.out.println("  din=" + din_val + " dout=" + dout_val);
				}
				
				din_idx++;
				dout_idx++;
				
				if (din_idx >= din_pages.get(din_page_idx).length) {
					System.out.println("DIN: next page");
					din_page_idx++;
					din_idx = 0;
				}
				if (dout_idx >= dout_pages.get(dout_page_idx).length){
					System.out.println("DOUT: next page");
					dout_page_idx++;
					dout_idx = 0;
				}
			}
			/*
			 */
		
			SVDBFile file2 = new SVDBFile();
			reader.init(din);
			reader.readObject(null, SVDBFile.class, file2);
			
		} catch (IOException e) {
			e.printStackTrace();
		} catch (DBFormatException e) {
			System.out.println("== Exception ==");
			e.printStackTrace();
		} catch (DBWriteException e) {
			e.printStackTrace();
		}

		List<SVDBDeclCacheItem> result = index.findGlobalScopeDecl(
				new NullProgressMonitor(), 
				"uvm_component", 
				SVDBFindDefaultNameMatcher.getDefault());

		System.out.println("Result: " + result.size());
		for (SVDBDeclCacheItem item : result) {
			System.out.println("Item: " + item.getName() + 
					" " + item.getType() + " " + item.getFilename());
			assertNotNull(item.getSVDBItem());
		}
		
		result = index.findGlobalScopeDecl(
				new NullProgressMonitor(), 
				"uvm_pkg", 
				SVDBFindDefaultNameMatcher.getDefault());

		System.out.println("Result: " + result.size());
		assertEquals(1, result.size());
		for (SVDBDeclCacheItem item : result) {
			System.out.println("Item: " + item.getName() + 
					" " + item.getType() + " " + item.getFilename());
			assertNotNull(item.getSVDBItem());
		}
		
		

		/**
		for (String path : index.getFileList(new NullProgressMonitor())) {
			System.out.println("Path: " + path);
			start = System.currentTimeMillis();
			SVDBFile file = index.findFile(path);
			end = System.currentTimeMillis();
			System.out.println("Extract " + path + " " + (end-start) + "ms");
			assertNotNull("Failed to find file " + path, file);
		}
		 */
	
		/*
		SVDBFile uvm_component_svh = index.findFile(
				new File(fTmpDir, "uvm/src/base/uvm_component.svh").getAbsolutePath());
		print("", uvm_component_svh);
		SVDBFile uvm_pkg_sv = index.findFile(
				new File(fTmpDir, "uvm/src/uvm_pkg.sv").getAbsolutePath());
		print("", uvm_pkg_sv);
		 */

	}

	public void testRebuildUVM() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().setTestDebugLevel(0);
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		IProject uvm = createProject("uvm", new File(fTmpDir, "uvm"));
		
		TestUtils.copy(
				"+define+QUESTA\n" +
				"+incdir+src\n" +
				"src/uvm_pkg.sv",
				uvm.getFile("uvm.f"));
		
		String base_location = "${workspace_loc}/uvm/uvm.f";

		ISVDBIndex index;
		
		index = createArgFileIndex(getName(), base_location, 
				new SVDBWSFileSystemProvider(), 
				fPrvCacheMgr.createIndexCache(getName(), base_location));
		
		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));
		
		List<SVDBDeclCacheItem> result;
		
		result = index.findGlobalScopeDecl(
				new NullProgressMonitor(), 
				"uvm_pkg", 
				SVDBFindDefaultNameMatcher.getDefault());
		assertEquals(1, result.size());
		
		result = index.findGlobalScopeDecl(
				new NullProgressMonitor(), 
				"uvm_pkg", 
				SVDBFindDefaultNameMatcher.getDefault());
		assertEquals(1, result.size());
	}


	
//	public void testFileSystemConstSize() {
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
//		SVCorePlugin.getDefault().setTestDebugLevel(0);
//		
//		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
//		
//		TestUtils.copy(
//				"+incdir+uvm/src\n" +
//				"uvm/src/uvm_pkg.sv",
//				new File(fTmpDir, "uvm.f"));
//		
//		String base_location = new File(fTmpDir, "uvm.f").getAbsolutePath();
//		
//		SVDBArgFileIndex2 index = new SVDBArgFileIndex2(
//				getName(), base_location,
//				new SVDBWSFileSystemProvider(),
//				fCacheMgr.createIndexCache(getName(), base_location),
//				null);
//		
//		long start, end;
//		
//		start = System.currentTimeMillis();
//		index.init(new NullProgressMonitor(), null);
//		index.execIndexChangePlan(new NullProgressMonitor(), 
//				new SVDBIndexChangePlanRebuild(index));
//		end = System.currentTimeMillis();
//		System.out.println("Parse UVM in " + (end-start) + "ms");
//
//		// For some unknown (yet) reason, the size after the first
//		// build is too large
//		fCacheMgr.sync();
//
//		int last_rebuild_sz = -1;
//		for (int i=0; i<4; i++) {
//			index.execIndexChangePlan(new NullProgressMonitor(), 
//					new SVDBIndexChangePlanRebuild(index));
//			fCacheMgr.sync();
//			int sz = fCacheFS.blockSize();
//			if (last_rebuild_sz != -1) {
//				assertEquals("Check size for " + i, last_rebuild_sz, sz);
//			}
//			last_rebuild_sz = sz;
//		}
//
//	}

//	public void testFileSystemConstSizeLibIndex() {
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
//		SVCorePlugin.getDefault().setTestDebugLevel(0);
//		
//		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
//		
//		TestUtils.copy(
//				"+incdir+uvm/src\n" +
//				"uvm/src/uvm_pkg.sv",
//				new File(fTmpDir, "uvm.f"));
//		
//		String base_location = new File(fTmpDir, "uvm/src/uvm_pkg.sv").getAbsolutePath();
//		
//		SVDBLibIndex index = new SVDBLibIndex(
//				getName(), base_location,
//				new SVDBWSFileSystemProvider(),
//				fCacheMgr.createIndexCache(getName(), base_location),
//				null);
//		
//		long start, end;
//		
//		start = System.currentTimeMillis();
//		index.init(new NullProgressMonitor(), null);
//		index.execIndexChangePlan(new NullProgressMonitor(), 
//				new SVDBIndexChangePlanRebuild(index));
//		end = System.currentTimeMillis();
//		System.out.println("Parse UVM in " + (end-start) + "ms");
//	
//		fCacheMgr.sync();
//		int first_rebuild_sz = fCacheFS.blockSize();
//
//		for (int i=0; i<4; i++) {
//			System.out.println("--> Build " + i);
//			index.execIndexChangePlan(new NullProgressMonitor(), 
//					new SVDBIndexChangePlanRebuild(index));
//			fCacheMgr.sync();
//			System.out.println("<-- Build " + i);
//		}
//
//		int second_rebuild_sz = fCacheFS.blockSize();
//		
//		assertEquals(first_rebuild_sz, second_rebuild_sz);
//	}

	public void testMFCU_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		TestUtils.copy(
				"// File1\n" +
				"`define FOO(n) class n; endclass\n" +
				"`FOO(cls1)\n",
				new File(fTmpDir, "file1.sv"));
		
		TestUtils.copy(
				"// File2\n" +
				"`FOO(cls2)\n\n\n\n",
				new File(fTmpDir, "file2.sv"));

		TestUtils.copy(
				"// mfcu.f\n" +
				"-mfcu\n" +
				"file1.sv\n" +
				"file2.sv\n",
				new File(fTmpDir, "mfcu.f"));
		
		String base_location = new File(fTmpDir, "mfcu.f").getAbsolutePath();
		
		SVDBArgFileIndex index = new SVDBArgFileIndex(
				getName(), base_location,
				new SVDBWSFileSystemProvider(),
				fPrvCacheMgr.createIndexCache(getName(), base_location),
				null);
		
		index.init(new NullProgressMonitor(), null);

		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));

		IndexTestUtils.assertFileHasElements(index, "cls1", "cls2");
	}

	public void testMFCU_2() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		TestUtils.copy(
				"// File1\n" +
				"`define FOO(n) class n; endclass\n",
				new File(fTmpDir, "file1.h"));
		
		TestUtils.copy(
				"// File2\n" +
				"`FOO(cls2)\n\n\n\n",
				new File(fTmpDir, "file2.sv"));

		TestUtils.copy(
				"// mfcu.f\n" +
				"-mfcu\n" +
				"file1.h\n" +
				"file2.sv\n",
				new File(fTmpDir, "mfcu.f"));
		
		String base_location = new File(fTmpDir, "mfcu.f").getAbsolutePath();
		
		SVDBArgFileIndex index = new SVDBArgFileIndex(
				getName(), base_location,
				new SVDBWSFileSystemProvider(),
				fPrvCacheMgr.createIndexCache(getName(), base_location),
				null);
		
		index.init(new NullProgressMonitor(), null);

		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));

		IndexTestUtils.assertFileHasElements(index, "cls2");
	}

	/*
	private void print(String ind, ISVDBChildParent parent) {
		System.out.println(ind + parent.getType() + " " + SVDBItem.getName(parent));
	
		ind += "  ";
		for (ISVDBChildItem c : parent.getChildren()) {
			if (c instanceof ISVDBChildParent) {
				print(ind, (ISVDBChildParent)c);
			} else {
				System.out.println(ind + c.getType() + " " + SVDBItem.getName(parent));
			}
		}
	}
	 */

	public void testParseUltraSPARC() {
//		SVCorePlugin.getDefault().setTestDebugLevel(2);
//		SVCorePlugin.getDefault().setTestDebugLevel(1);
	
		String base_location = "/home/ballance.2/Downloads/OpenSPARCT2/design/design.f";
		
		SVDBArgFileIndex index = new SVDBArgFileIndex(
				getName(), base_location,
				new SVDBWSFileSystemProvider(),
				fPrvCacheMgr.createIndexCache(getName(), base_location),
				null);
		
		long start, end;
		
		start = System.currentTimeMillis();
		SVDBIndexBuilder builder = new SVDBIndexBuilder();
		index.init(new NullProgressMonitor(), builder /*SVCorePlugin.getDefault().getIndexBuilder()*/);
		index.loadIndex(new NullProgressMonitor());
		end = System.currentTimeMillis();
		
		System.out.println("Parse UltraSPARC in " + (end-start) + "ms");

		boolean try_reload = false;
		if (try_reload) {
		start = System.currentTimeMillis();
		int n_files = 0;
		for (int i=0; i<8; i++) {
			n_files = 0;
			for (String path : index.getFileList(new NullProgressMonitor())) {
				//			System.out.println("Path: " + path);
				//			start = System.currentTimeMillis();
				SVDBFile file = index.findFile(path);
				//			end = System.currentTimeMillis();
				//			System.out.println("Extract " + path + " " + (end-start) + "ms");
				assertNotNull("Failed to find file " + path, file);
				n_files++;
			}
		} 
		end = System.currentTimeMillis();

		System.out.println("Iterate through " + n_files + " 100 times: " + (end-start) + "ms");
		}
		boolean try_rand_sel = true;
		if (try_rand_sel) {
			List<String> paths = new ArrayList<String>();
			for (String path : index.getFileList(new NullProgressMonitor())) {
				paths.add(path);
			}
			Random rn = new Random();
			int n = 40; /* paths.size(); */ 
			int n_files = 1000;
			
			start = System.currentTimeMillis();
			for (int i=0; i<n_files; i++) {
				int idx = rn.nextInt() % n;
				if (idx < 0) {
					idx = -idx;
				}
				String path = paths.get(idx);
				SVDBFile file = index.findFile(path);
				assertNotNull("Failed to find file " + path, file);
			}
			end = System.currentTimeMillis();
			System.out.println("Iterate through " + n_files + " 100 times: " + (end-start) + "ms");
		} 

	}

	public void testParseUltraSPARC2() {
//		SVCorePlugin.getDefault().setTestDebugLevel(2);
//		SVCorePlugin.getDefault().setTestDebugLevel(1);
	
		String base_location = "/home/ballance.2/Downloads/OpenSPARCT2/design/design.f";
		
		String target = "/home/ballance.2/Downloads/OpenSPARCT2/design/sys/iop/tds/rtl/tds_n2_efuhdr2_msff_ctl_macro__width_4.v";
		File argfile = new File(fTmpDir, "argfile.f");

		TestUtils.copy(
				target,
				argfile);
	
		base_location = argfile.getAbsolutePath();
		
		SVDBArgFileIndex index = new SVDBArgFileIndex(
				getName(), base_location,
				new SVDBWSFileSystemProvider(),
				fPrvCacheMgr.createIndexCache(getName(), base_location),
				null);
		
		long start, end;
		
		start = System.currentTimeMillis();
		index.init(new NullProgressMonitor(), SVCorePlugin.getDefault().getIndexBuilder());
		index.loadIndex(new NullProgressMonitor());
		end = System.currentTimeMillis();

/*		SVDBFileIndexCacheMgr mgr = (SVDBFileIndexCacheMgr)fCacheMgr; */
		SVDBFileIndexCache cache = (SVDBFileIndexCache)index.getCache();
		
		IDBWriter writer = new SVDBPersistenceRW();
		IDBReader reader = new SVDBPersistenceRW();
		
		Set<String> files = cache.getFileList(false);
		SVDBFile file = cache.getFile(new NullProgressMonitor(), files.iterator().next());
	
		File db3 = new File(fTmpDir, "db3");
		SVDBFileSystem fs = new SVDBFileSystem(db3, SVCorePlugin.getVersion());
		try {
			fs.init();
			
			SVDBFileSystemDataOutput dout = new SVDBFileSystemDataOutput();
			SVDBFileSystemDataInput  din;
			
			writer.init(dout);
			
			writer.writeObject(SVDBFile.class, file);
			
			int fileid = fs.writeFile("dout", dout);
			
			din = fs.readFile("dout", fileid);
			
//			din.fDebugEn = true;
		
			int len = dout.getLength();
			List<byte[]> din_pages = din.getPages();
			List<byte[]> dout_pages = dout.getPages();
			int dout_idx=0;
			int din_idx=din.getPageIdx();
			int din_page_idx=din.getPagesIdx();
			int dout_page_idx=0;
	
			System.out.println("init: din_page_idx=" + din_page_idx);
			System.out.println("init: din_idx=" + din_idx);
			System.out.println("init: dout_page_idx=" + dout_page_idx);
			System.out.println("init: dout_idx=" + dout_idx);
			
			for (int i=0; i<len; i++) {
				int din_val  = din_pages.get(din_page_idx)[din_idx];
				int dout_val = dout_pages.get(dout_page_idx)[dout_idx];
				
//				System.out.println("din_val=" + din_val + " dout_val=" + dout_val);
				
				if (din_val != dout_val) {
					System.out.println("[ERROR] @ " + din_page_idx + ":" + din_idx +
							" " + dout_page_idx + ":" + dout_idx);
					System.out.println("  din=" + din_val + " dout=" + dout_val);
				}
				
				din_idx++;
				dout_idx++;
				
				if (din_idx >= din_pages.get(din_page_idx).length) {
					System.out.println("DIN: next page");
					din_page_idx++;
					din_idx = 0;
				}
				if (dout_idx >= dout_pages.get(dout_page_idx).length){
					System.out.println("DOUT: next page");
					dout_page_idx++;
					dout_idx = 0;
				}
			}
			/*
			 */
		
			SVDBFile file2 = new SVDBFile();
			reader.init(din);
			reader.readObject(null, SVDBFile.class, file2);
			
		} catch (IOException e) {
			e.printStackTrace();
		} catch (DBFormatException e) {
			System.out.println("== Exception ==");
			e.printStackTrace();
		} catch (DBWriteException e) {
			e.printStackTrace();
		}
		
		System.out.println("Parse UVM in " + (end-start) + "ms");
		
		for (String path : index.getFileList(new NullProgressMonitor())) {
			System.out.println("Path: " + path);
			start = System.currentTimeMillis();
			/*SVDBFile*/ file = index.findFile(path);
			end = System.currentTimeMillis();
			System.out.println("Extract " + path + " " + (end-start) + "ms");
			assertNotNull("Failed to find file " + path, file);
		}
		
	
		/*
		SVDBFile uvm_component_svh = index.findFile(
				new File(fTmpDir, "uvm/src/base/uvm_component.svh").getAbsolutePath());
		print("", uvm_component_svh);
		SVDBFile uvm_pkg_sv = index.findFile(
				new File(fTmpDir, "uvm/src/uvm_pkg.sv").getAbsolutePath());
		print("", uvm_pkg_sv);
		 */

	}
	
}
