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
import java.net.URL;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestParserPerf extends TestCase {
	
	private File				fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
	}



	@Override
	protected void tearDown() throws Exception {
//		TestUtils.delete(fTmpDir);
		// TODO Auto-generated method stub
		super.tearDown();
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
//		rgy.test_init(TestIndexCacheFactory.instance(null));
		rgy.test_init(TestIndexCacheFactory.instance(fTmpDir));
		
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

	public void testUVMPreProc() {
		/*
		LogFactory.getDefault().addLogListener(new ILogListener() {
			
			public void message(ILogHandle handle, int type, int level, String message) {
				System.out.println("[MSG] " + message);
			}
		});
		 */
//		LogFactory.getDefault().setLogLevel(null, 10);
		
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

		SVDBIndexRegistry rgy = new SVDBIndexRegistry(true);
		SVDBLibPathIndexFactory factory = new SVDBLibPathIndexFactory();
//		rgy.test_init(TestIndexCacheFactory.instance(null));
		rgy.test_init(TestIndexCacheFactory.instance(fTmpDir));
	
		File uvm = new File(fTmpDir, "uvm");
		File uvm_pkg = new File(uvm, "src/uvm_pkg.sv");
		
		System.out.println("uvm_pkg: " + uvm_pkg.getAbsolutePath());

		ISVDBIndex index = rgy.findCreateIndex("GENERIC",
				uvm_pkg.getAbsolutePath(), 
				SVDBLibPathIndexFactory.TYPE, 
				factory, 
				null);
		
		// ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		long fullparse_start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long fullparse_end = System.currentTimeMillis();
		
		System.out.println("Full parse: " + (fullparse_end-fullparse_start));
		System.out.println("Files: " + index.getFileList(new NullProgressMonitor()).size());
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
	
	public void testOpenSparc() {
		File opensparc_design = new File("/home/ballance.1/Downloads/OpenSPARCT2/design/design.f");

		SVDBIndexRegistry rgy = new SVDBIndexRegistry(true);
		SVDBArgFileIndexFactory factory = new SVDBArgFileIndexFactory();
		rgy.test_init(TestIndexCacheFactory.instance(fTmpDir));
		
		ISVDBIndex index = rgy.findCreateIndex("GENERIC",
				opensparc_design.getAbsolutePath(), 
				SVDBArgFileIndexFactory.TYPE, factory, null);
		
		// ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		long fullparse_start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long fullparse_end = System.currentTimeMillis();
		System.out.println("Full parse: " + (fullparse_end-fullparse_start));
		System.out.println("Files: " + index.getFileList(new NullProgressMonitor()).size());
	}
}
