/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.parser.perf;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBIndexStats;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex2;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVLanguageLevel;
import net.sf.sveditor.core.parser.SVLexer;
import net.sf.sveditor.core.parser.SVParser;
import net.sf.sveditor.core.preproc.SVPathPreProcIncFileProvider;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor2;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestParserPerf extends SVCoreTestCaseBase {
	
	private String				fTestPluginPath;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();

		SVCorePlugin.testInit();
		SVCorePlugin.getDefault().setDebugLevel(ILogLevel.LEVEL_MID);
		
		String cls_path = "net/sf/sveditor/core/tests/CoreReleaseTests.class";
		URL plugin_class = getClass().getClassLoader().getResource(cls_path);
		System.out.println("plugin_class: " + plugin_class.toExternalForm());
		String path = plugin_class.toExternalForm();
		path = path.substring("file:".length());
		path = path.substring(0, path.length()-(cls_path.length()+"/class/".length()));		
		
		fTestPluginPath = path;
		
//		SVCorePlugin.testInit(); 
	}

	public void testXBusExample() {
		/*
		LogFactory.getDefault().addLogListener(new ILogListener() {
			
			public void message(ILogHandle handle, int type, int level, String message) {
				System.out.println("[MSG] " + message);
			}
		});
		 */
		
		String cls_path = "net/sf/sveditor/core/tests/CoreReleaseTests.class";
		URL plugin_class = getClass().getClassLoader().getResource(cls_path);
		System.out.println("plugin_class: " + plugin_class.toExternalForm());
		String path = plugin_class.toExternalForm();
		path = path.substring("file:".length());
		path = path.substring(0, path.length()-(cls_path.length()+"/class/".length()));
		
		String ovm_dir = path + "/ovm";

//		SVCorePlugin.getDefault().enableDebug(false);
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		String xbus = ovm_dir + "/examples/xbus";

		SVDBIndexRegistry rgy = new SVDBIndexRegistry(true);
		SVDBArgFileIndexFactory factory = new SVDBArgFileIndexFactory();
		rgy.test_init(fCacheFactory);
		
		String compile_questa_sv = xbus + "/examples/compile_questa_sv.f";
		System.out.println("compile_questa_sv=" + compile_questa_sv);
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC",
				compile_questa_sv, SVDBArgFileIndexFactory.TYPE, factory, null);
		
		// ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		index.loadIndex(new NullProgressMonitor());
		/*
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)tmp_it;
				if (m.getMarkerType() == MarkerType.Error) {
					errors.add(m);
				}
			}
			
			//System.out.println("tmp_it=" + tmp_it.getName());
		}
		
		for (SVDBMarker m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
		 */
	}

	public void testUVMPreProc() throws IOException {
		/*
		LogFactory.getDefault().addLogListener(new ILogListener() {
			
			public void message(ILogHandle handle, int type, int level, String message) {
				System.out.println("[MSG] " + message);
			}
		});
		 */
//		LogFactory.getDefault().setLogLevel(null, 10);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String cls_path = "net/sf/sveditor/core/tests/CoreReleaseTests.class";
		URL plugin_class = getClass().getClassLoader().getResource(cls_path);
		System.out.println("plugin_class: " + plugin_class.toExternalForm());
		String path = plugin_class.toExternalForm();
		path = path.substring("file:".length());
		path = path.substring(0, path.length()-(cls_path.length()+"/class/".length()));
		
		File uvm_zip = new File(new File(path), "/uvm.zip");

//		SVCorePlugin.getDefault().enableDebug(false);
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		TestUtils.unpackZipToFS(uvm_zip, fTmpDir);

		TestIndexCacheFactory factory = fCacheFactory;
	
		File uvm = new File(fTmpDir, "uvm");
		File uvm_pkg = new File(uvm, "src/uvm_pkg.sv");
		
		System.out.println("uvm_pkg: " + uvm_pkg.getAbsolutePath());
	
		File uvm_f = new File(uvm, "uvm.f");
		PrintStream ps = new PrintStream(uvm_f);
		ps.println("+define+MODEL_TECH");
		ps.println("+define+QUESTA");
		ps.println("+incdir+./src");
		ps.println("src/uvm_pkg.sv");
		ps.close();

		ISVDBIndex index;
		
			index = new SVDBArgFileIndex2("GENERIC", 
					uvm_f.getAbsolutePath(),
					new SVDBFSFileSystemProvider(),
					factory.createIndexCache("GENERIC",  uvm_f.getAbsolutePath()),
					null);
		
		index.init(new NullProgressMonitor(), null);
		
		// ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		long fullparse_start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long fullparse_end = System.currentTimeMillis();
		
		System.out.println("Full parse: " + (fullparse_end-fullparse_start));
//		System.out.println("Files: " + index.getFileList(new NullProgressMonitor()).size());
		/*
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)tmp_it;
				if (m.getMarkerType() == MarkerType.Error) {
					errors.add(m);
				}
			}
			
			//System.out.println("tmp_it=" + tmp_it.getName());
		}
		
		for (SVDBMarker m : errors) {
			System.out.println("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
		 */
	}	

	public void testUVMPreProcPerf() throws IOException, InterruptedException {
		/*
		LogFactory.getDefault().addLogListener(new ILogListener() {
			
			public void message(ILogHandle handle, int type, int level, String message) {
				System.out.println("[MSG] " + message);
			}
		});
		 */
//		LogFactory.getDefault().setLogLevel(null, 10);
		SVCorePlugin.getDefault().enableDebug(false);
		
		String cls_path = "net/sf/sveditor/core/tests/CoreReleaseTests.class";
		URL plugin_class = getClass().getClassLoader().getResource(cls_path);
		System.out.println("plugin_class: " + plugin_class.toExternalForm());
		String path = plugin_class.toExternalForm();
		path = path.substring("file:".length());
		path = path.substring(0, path.length()-(cls_path.length()+"/class/".length()));
		
		File uvm_zip = new File(new File(path), "/uvm.zip");

//		SVCorePlugin.getDefault().enableDebug(false);
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		TestUtils.unpackZipToFS(uvm_zip, fTmpDir);

//		TestIndexCacheFactory factory = fCacheFactory;
	
		File uvm = new File(fTmpDir, "uvm");
		File uvm_pkg = new File(uvm, "src/uvm_pkg.sv");
		InputStream in = new FileInputStream(uvm_pkg);
		
		System.out.println("uvm_pkg: " + uvm_pkg.getAbsolutePath());

		/*
		System.out.println("--> Sleeping");
		Thread.sleep(10000);
		System.out.println("<-- Sleeping");
		 */

		SVPathPreProcIncFileProvider inc_provider = new SVPathPreProcIncFileProvider(
				new SVDBFSFileSystemProvider());
		inc_provider.addIncdir(new File(uvm, "src").getAbsolutePath());
		SVPreProcessor2 pp = new SVPreProcessor2(uvm_pkg.getAbsolutePath(), 
				in, inc_provider, null);
		
		in.close();
	
		SVDBIndexStats stats = new SVDBIndexStats();
		pp.setIndexStats(stats);
	
		long pp_start = System.currentTimeMillis();
		SVPreProcOutput pp_out = pp.preprocess();
		long pp_end = System.currentTimeMillis();
		System.out.println("Pre-Process: " + (pp_end-pp_start));

		if (true) {
		return;
		}
		
		SVPreProcOutput pp_out_parse = pp_out.duplicate();
		
		SVLexer l = new SVLexer();
		l.init(null, pp_out);
		
		long lex_start = System.currentTimeMillis();
		int tcount = 0;
		while (l.eatTokenR() != null) {
			tcount++;
		}
		long lex_end = System.currentTimeMillis();
		
		System.out.println("Processed " + tcount + " tokens in " + (lex_end-lex_start) + "ms");
	
		SVParser ff = new SVParser();
		List<SVDBMarker> m = new ArrayList<SVDBMarker>();
		long parse_start = System.currentTimeMillis();
		ff.parse(SVLanguageLevel.SystemVerilog, pp_out_parse, "", m);
		long parse_end = System.currentTimeMillis();
		System.out.println("Parse: " + (parse_end-parse_start));
		

		System.out.println("Index Stats:\n" + stats.toString());
	}	
	
	public void testManyIfdefs() {
	
		SVCorePlugin.testInit();
		SVCorePlugin.getDefault().setDebugLevel(ILogLevel.LEVEL_MID);
		
		String cls_path = "net/sf/sveditor/core/tests/CoreReleaseTests.class";
		URL plugin_class = getClass().getClassLoader().getResource(cls_path);
		System.out.println("plugin_class: " + plugin_class.toExternalForm());
		String path = plugin_class.toExternalForm();
		path = path.substring("file:".length());
		path = path.substring(0, path.length()-(cls_path.length()+"/class/".length()));
		
		File proj_zip = new File(new File(path), "/data/performance/many_ifdefs/ProjectIncdir.zip");

		TestUtils.unpackZipToFS(proj_zip, fTmpDir);

		SVDBIndexRegistry rgy = new SVDBIndexRegistry(true);
		SVDBArgFileIndexFactory factory = new SVDBArgFileIndexFactory();
		rgy.test_init(fCacheFactory);
	
		File project_incdir = new File(fTmpDir, "ProjectIncdir");
		File project_incdir_f = new File(project_incdir, "ProjectIncdir.f");
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC",
				project_incdir_f.getAbsolutePath(), 
				SVDBArgFileIndexFactory.TYPE,
				factory, 
				null);
		
		long fullparse_start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long fullparse_end = System.currentTimeMillis();
		
		System.out.println("Full parse: " + (fullparse_end-fullparse_start));
	}
	
	public void testOpenSparc() {
		/*
		System.out.println("BEGIN");
		try {
			Thread.sleep(15000);
		} catch (InterruptedException e) {}
		System.out.println("END");
		 */
		
		SVCorePlugin.getDefault().enableDebug(false);
		File opensparc_design = new File("/home/ballance.1/Downloads/OpenSPARCT2/design/design.f");
		TestIndexCacheFactory cache_f = fCacheFactory;
		
		ISVDBIndex index;
		
			index = new SVDBArgFileIndex2("GENERIC", opensparc_design.getAbsolutePath(), 
					new SVDBFSFileSystemProvider(), 
					cache_f.createIndexCache("GENERIC", opensparc_design.getAbsolutePath()),
					null);
		index.init(new NullProgressMonitor(), null);
		
		// ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		long fullparse_start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long fullparse_end = System.currentTimeMillis();
		System.out.println("Full parse: " + (fullparse_end-fullparse_start));
//		System.out.println("Files: " + index.getFileList(new NullProgressMonitor()).size());
	}

	public void testOpenSparc2() {
		File opensparc_design = new File("/home/ballance.1/Downloads/OpenSPARCT2/design/design.f");

		TestIndexCacheFactory cache_f = fCacheFactory;
		
		ISVDBIndex index = new SVDBArgFileIndex2("GENERIC", 
				opensparc_design.getAbsolutePath(),
				new SVDBFSFileSystemProvider(),
				cache_f.createIndexCache("GENERIC", opensparc_design.getAbsolutePath()),
				null);
		index.init(new NullProgressMonitor(), null);
				
		long fullparse_start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long fullparse_end = System.currentTimeMillis();
		System.out.println("Full parse: " + (fullparse_end-fullparse_start));
		
		Iterable<String> files = index.getFileList(new NullProgressMonitor());
	
		/*
		for (String f : files) {
			System.out.println("File: " + f);
			SVDBFile p = index.findFile(f);
			traverse_files(p, -1);
//			break;
		}
		 */
	}

	public void testUVM2() {
		File opensparc_design = new File("/tools/uvm/uvm-1.1a/uvm.f");

		TestIndexCacheFactory cache_f = fCacheFactory;
		
		ISVDBIndex index = new SVDBArgFileIndex2("GENERIC", 
				opensparc_design.getAbsolutePath(),
				new SVDBFSFileSystemProvider(),
				cache_f.createIndexCache("GENERIC", opensparc_design.getAbsolutePath()),
				null);
		index.init(new NullProgressMonitor(), null);
				
		long fullparse_start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long fullparse_end = System.currentTimeMillis();
		System.out.println("Full parse: " + (fullparse_end-fullparse_start));
		
		Iterable<String> files = index.getFileList(new NullProgressMonitor());
		
		for (String f : files) {
			System.out.println("File: " + f);
			SVDBFile p = index.findFile(f);
			traverse_files(p, -1);
//			break;
		}
	}
	private void traverse_files(ISVDBChildParent p, int file_id) {
		for (ISVDBChildItem c : p.getChildren()) {
			System.out.println("Item: " + SVDBItem.getName(c));
			if (c.getLocation() != -1 && SVDBLocation.unpackFileId(c.getLocation()) != file_id) {
				System.out.println("Switch to file: " + SVDBLocation.unpackFileId(c.getLocation()));
				file_id = SVDBLocation.unpackFileId(c.getLocation());
			}

			if (c instanceof ISVDBChildParent) {
				traverse_files((ISVDBChildParent)c, file_id);
			} else if (c instanceof ISVDBScopeItem) {
				
			}
		}
		
	}

	public void testLargeParam() {
		File opensparc_design = new File("/home/ballance/Downloads/sz/Project_complicated_include/top_dir/files.f");

		TestIndexCacheFactory cache_f = fCacheFactory;
		
		ISVDBIndex index = new SVDBArgFileIndex2("GENERIC", 
				opensparc_design.getAbsolutePath(),
				new SVDBFSFileSystemProvider(),
				cache_f.createIndexCache("GENERIC", opensparc_design.getAbsolutePath()),
				null);
		index.init(new NullProgressMonitor(), null);
				
		long fullparse_start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long fullparse_end = System.currentTimeMillis();
		System.out.println("Full parse: " + (fullparse_end-fullparse_start));
	}
	
	public void testLargeParam2() {
		File opensparc_design = new File("/home/ballance/Downloads/sz/Project_complicated_include/top_dir/files.f");

		TestIndexCacheFactory cache_f = fCacheFactory;
		
		ISVDBIndex index = new SVDBArgFileIndex2("GENERIC", 
				opensparc_design.getAbsolutePath(),
				new SVDBFSFileSystemProvider(),
				cache_f.createIndexCache("GENERIC", opensparc_design.getAbsolutePath()),
				null);
		index.init(new NullProgressMonitor(), null);
				
		long fullparse_start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long fullparse_end = System.currentTimeMillis();
		System.out.println("Full parse: " + (fullparse_end-fullparse_start));
	}	
	
	public void testEthernetExample() {
		LogHandle log = LogFactory.getLogHandle("testEthernetExample");
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);
		
		File test_dir = new File(fTmpDir, "testEthernetExample");
		if (test_dir.exists()) {
			TestUtils.delete(test_dir);
		}
		test_dir.mkdirs();

		File vmm_zip = new File(fTestPluginPath, "vmm.zip");
		TestUtils.unpackZipToFS(vmm_zip, test_dir);
		
		File ethernet_f = new File(test_dir, "vmm/sv/examples/std_lib/ethernet/ethernet.f");
	
//		IProject project = TestUtils.createProject("ethernet", ethernet);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			TestUtils.delete(db);
		}

		TestIndexCacheFactory cache_f = fCacheFactory;
		
		ISVDBIndex index = null;
		
			index = new SVDBArgFileIndex2("GENERIC", 
				ethernet_f.getAbsolutePath(),
				new SVDBFSFileSystemProvider(),
				cache_f.createIndexCache("GENERIC", ethernet_f.getAbsolutePath()),
				null);
		index.init(new NullProgressMonitor(), null);
	
		long start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long end = System.currentTimeMillis();
		System.out.println("Load: " + (end-start) + "ms");

		/*
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		int count = 0;
		while (it.hasNext()) {
			ISVDBItemBase tmp_it = it.nextItem();
			
			if (tmp_it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)tmp_it;
				if (m.getMarkerType() == MarkerType.Error) {
					errors.add(m);
				}
			}
			
			log.debug("tmp_it=" + SVDBItem.getName(tmp_it));
		}
		
		for (SVDBMarker m : errors) {
			log.debug("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
		 */
		LogFactory.removeLogHandle(log);
	}	
}
