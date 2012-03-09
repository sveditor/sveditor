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


package net.sf.sveditor.core.tests.index.persistence;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInput;
import java.io.DataInputStream;
import java.io.DataOutput;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.io.RandomAccessFile;
import java.net.URL;
import java.util.Set;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceRWDelegate;
import net.sf.sveditor.core.db.persistence.JITSVDBExprDelegateFactory;
import net.sf.sveditor.core.db.persistence.SVDBDelegatingPersistenceRW;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceRW;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.TestNullIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.osgi.framework.Bundle;

public class TestPersistencePerformance extends TestCase {

	private File			fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		if (fTmpDir != null) {
//			TestUtils.delete(fTmpDir);
		}
	}
	
	public void testJITPersistence() throws Exception {
		SVDBInclude inc = new SVDBInclude("foo");
		inc.setLocation(new SVDBLocation(1, 1));
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		DataOutputStream out = new DataOutputStream(bos);
		DataInputStream in;
		long start, end;
		
		SVDBDelegatingPersistenceRW dflt1 = new SVDBDelegatingPersistenceRW() {

			@Override
			public void writeEnumType(Class enum_type, Enum value)
					throws DBWriteException {
				// TODO Auto-generated method stub
				System.out.println("writeEnumType");
				super.writeEnumType(enum_type, value);
			}

			@Override
			public void writeString(String val) throws DBWriteException {
				// TODO Auto-generated method stub
				System.out.println("writeString " + val);
				super.writeString(val);
			}

			@Override
			public SVDBLocation readSVDBLocation() throws DBFormatException {
				System.out.println("readSVDBLocation");
				return super.readSVDBLocation();
			}

			@Override
			public void writeSVDBLocation(SVDBLocation loc)
					throws DBWriteException {
//				System.out.println("writeSVDBLocation");
				super.writeSVDBLocation(loc);
			}
			
			
		};
		SVDBDelegatingPersistenceRW dflt = new SVDBDelegatingPersistenceRW();
		ISVDBPersistenceRWDelegate delegate = JITSVDBExprDelegateFactory.instance().newDelegate();
//		ISVDBPersistenceRWDelegate delegate = new SVDBDefaultPersistenceRW();
		int n_iter = 1000000;
		dflt.init(out);
		delegate.init(dflt, null, null);
		start = System.currentTimeMillis(); 
		for (int i=0; i<n_iter; i++) {
			delegate.writeSVDBItem(inc);
		}
		
		in = new DataInputStream(new ByteArrayInputStream(bos.toByteArray()));
		dflt.init(in);
		for (int i=0; i<n_iter; i++) {
			SVDBInclude inc_1 = (SVDBInclude)delegate.readSVDBItem(SVDBItemType.Include, null);
		}
		end = System.currentTimeMillis();
		
		System.out.println("" + n_iter + " items in " + (end-start));
//		System.out.println("inc_1: " + inc_1.getName());
//		System.out.println("    location: " + inc_1.getLocation().getLine());
	}

	public void testInMemPersistence() throws IOException, CoreException, DBFormatException, DBWriteException {
		IDBWriter writer = new SVDBPersistenceRW();
		IDBReader reader = new SVDBPersistenceRW();
		
		ByteArrayOutputStream bos = null;
		Bundle bundle = SVCorePlugin.getDefault().getBundle(); 
		URL cls_url = bundle.getEntry("/sv_builtin/string.svh");
		InputStream cls_in = cls_url.openStream();
		String content = TestUtils.readInput(cls_in);
		SVDBFile file = SVDBTestUtils.parse(content, "string.svh");
		
		try {
			cls_in.close();
		} catch (IOException e) {}

		bos = new ByteArrayOutputStream();
		DataOutput out = new DataOutputStream(bos);
		writer.init(out);
		writer.writeSVDBItem(file);

		long start = System.currentTimeMillis();
		for (int i=0; i<10000; i++) {
			ByteArrayInputStream ba_in = new ByteArrayInputStream(bos.toByteArray());
			DataInput in = new DataInputStream(ba_in);
			
			reader.init(in);
			reader.readSVDBItem(null);
		}
		long end = System.currentTimeMillis();
		
		System.out.println("1000 loads in " + (end-start) + "ms");
	}

	public void testFSPerf() throws IOException, CoreException, DBFormatException, DBWriteException {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testFSPerf");
		
		File test_dir = new File(fTmpDir, "testFSPerf");
		if (test_dir.exists()) {
			TestUtils.delete(test_dir);
		}
		test_dir.mkdirs();
		
		utils.unpackBundleZipToFS("/uvm.zip", test_dir);		
		File ubus = new File(test_dir, "uvm/examples/integrated/ubus");
		
		IProject project_dir = TestUtils.createProject("ubus", ubus);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		db.mkdirs();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(new TestNullIndexCacheFactory());
		
		PrintStream ps = new PrintStream(new File(ubus, "/examples/questa.f"));
		ps.println("+incdir+../sv");
		ps.println("+incdir+../../../../src");
		ps.println("../../../../src/uvm_pkg.sv");
		ps.println("ubus_tb_top.sv");
		ps.flush();
		ps.close();
		
		ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/ubus/examples/questa.f",
				SVDBArgFileIndexFactory.TYPE, null);

		Set<String> files = index.getFileList(new NullProgressMonitor());
//		SVDBDelegatingPersistenceRW delegate = SVDBDelegatingPersistenceRW.createDefault();
		SVDBPersistenceRW delegate = new SVDBPersistenceRW();

//		IDBWriter writer = new SVDBPersistenceRW();
//		IDBReader reader = new SVDBPersistenceRW();
		IDBWriter writer = delegate;
		IDBReader reader = delegate;

		long start = System.currentTimeMillis(), end, total_time;
		int iter=10;
		int total = 0;
		/*
		for (int i=0; i<iter; i++) {
			FileOutputStream fos = new FileOutputStream(new File(db, "file_" + i));
			DataOutputStream dos = new DataOutputStream(fos);
			writer.init(dos);
			
			for (String file : files) {
				SVDBFile svdb_file = index.findFile(file);
				writer.writeSVDBItem(svdb_file);
				total++;
			}
			
			dos.close();
			fos.close();
		}
		for (int i=0; i<iter; i++) {
			FileInputStream fis = new FileInputStream(new File(db, "file_" + i));
			DataInputStream dis = new DataInputStream(fis);
			reader.init(dis);
			
			for (String file : files) {
				ISVDBItemBase item = reader.readSVDBItem(null);
			}
			
			dis.close();
			fis.close();
		}
		end = System.currentTimeMillis();
		total_time = (end-start);
		
		if (total_time == 0) {
			total_time=1;
		}
		
		System.out.println("Performance: " + total + " items in " + total_time + "ms");
		System.out.println("    " + (total_time/total) + " ms/item");
		 */

		total=0;
//		RandomAccessFile af = new RandomAccessFile(new File(db, "file_r"), "rw");
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		DataOutput dout = new DataOutputStream(bos);
		DataInput din = null;
		
		/*
		byte data[] = new byte[1024*1024];
		for (int i=0; i<200; i++) {
			af.write(data);
		}
		 */
		
		start = System.currentTimeMillis();		
		for (int i=0; i<iter; i++) {
			writer.init(dout);
			
			for (String file : files) {
				// af.seek(1024*1024*total);
				SVDBFile svdb_file = index.findFile(file);
				writer.writeSVDBItem(svdb_file);
				total++;
			}
		}
		total=0;
		// af.seek(0);
		din = new DataInputStream(new ByteArrayInputStream(bos.toByteArray()));
		for (int i=0; i<iter; i++) {
			reader.init(din);
			
			for (String file : files) {
				// af.seek(1024*1024*total);
				ISVDBItemBase item = reader.readSVDBItem(null);
				total++;
			}
		}
		end = System.currentTimeMillis();
		total_time = (end-start);
		
		if (total_time == 0) {
			total_time=1;
		}

		System.out.println("Performance: " + total + " items in " + total_time + "ms");
		System.out.println("    " + (total_time/total) + " ms/item");

		LogFactory.removeLogHandle(log);
		TestUtils.deleteProject(project_dir);
	}
}
