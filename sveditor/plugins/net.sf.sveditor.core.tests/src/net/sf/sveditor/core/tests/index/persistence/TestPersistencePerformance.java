/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package net.sf.sveditor.core.tests.index.persistence;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInput;
import java.io.DataInputStream;
import java.io.DataOutput;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBInclude;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBBaseIndexCacheData;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexCacheData;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceRWDelegate;
import net.sf.sveditor.core.db.persistence.JITPersistenceDelegateFactory;
import net.sf.sveditor.core.db.persistence.SVDBDelegatingPersistenceRW;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceRW;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.osgi.framework.Bundle;

public class TestPersistencePerformance extends SVCoreTestCaseBase {

	public void testJITPersistence() throws Exception {
		SVDBInclude inc = new SVDBInclude("foo");
		inc.setLocation(SVDBLocation.pack(0, 1, 1));
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		DataOutputStream out = new DataOutputStream(bos);
		DataInputStream in;
		long start, end;
		
		SVDBDelegatingPersistenceRW dflt1 = new SVDBDelegatingPersistenceRW() {

			@Override
			public void writeEnumType(Class<?> enum_type, Enum<?> value)
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
		ISVDBPersistenceRWDelegate delegate = JITPersistenceDelegateFactory.instance().newDelegate();
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
		
		IProject project = TestUtils.createProject("ubus", ubus);
		addProject(project);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		db.mkdirs();
		
		PrintStream ps = new PrintStream(new File(ubus, "/examples/questa.f"));
		ps.println("+incdir+../sv");
		ps.println("+incdir+../../../../src");
		ps.println("../../../../src/uvm_pkg.sv");
		ps.println("ubus_tb_top.sv");
		ps.flush();
		ps.close();
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/ubus/examples/questa.f",
				SVDBArgFileIndexFactory.TYPE, null);

		Iterable<String> files = index.getFileList(new NullProgressMonitor());
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
	}

	public void testCacheDataPerf() throws IOException, CoreException, DBFormatException, DBWriteException {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		String testname = "testCacheDataPerf";
		LogHandle log = LogFactory.getLogHandle(testname);
		
		File test_dir = new File(fTmpDir, testname);
		if (test_dir.exists()) {
			TestUtils.delete(test_dir);
		}
		test_dir.mkdirs();
		
		utils.unpackBundleZipToFS("/uvm.zip", test_dir);		
		File ubus = new File(test_dir, "uvm/examples/integrated/ubus");
		
		IProject project = TestUtils.createProject("ubus", ubus);
		addProject(project);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		db.mkdirs();
		
		PrintStream ps = new PrintStream(new File(ubus, "/examples/questa.f"));
		ps.println("+incdir+../sv");
		ps.println("+incdir+../../../../src");
		ps.println("../../../../src/uvm_pkg.sv");
		ps.println("ubus_tb_top.sv");
		ps.flush();
		ps.close();
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/ubus/examples/questa.f",
				SVDBArgFileIndexFactory.TYPE, null);

		Iterable<String> files = index.getFileList(new NullProgressMonitor());
		SVDBPersistenceRW delegate = new SVDBPersistenceRW();

		IDBWriter writer = delegate;
		IDBReader reader = delegate;

		long start = System.currentTimeMillis(), end, total_time;
		int iter=1;
		int total = 0;

		total=0;
//		RandomAccessFile af = new RandomAccessFile(new File(db, "file_r"), "rw");
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		DataOutput dout = new DataOutputStream(bos);
		DataInput din = null;
		
		SVDBBaseIndexCacheData cd = new SVDBBaseIndexCacheData("base");
		SVDBBaseIndexCacheData cd2 = new SVDBBaseIndexCacheData("base");
		SVDBArgFileIndexCacheData acd = new SVDBArgFileIndexCacheData("base");
		SVDBArgFileIndexCacheData acd2 = new SVDBArgFileIndexCacheData("base");
		SVDBFile f = new SVDBFile("myfile");
		SVDBFile f2 = new SVDBFile();
		List<SVDBDeclCacheItem> items = new ArrayList<SVDBDeclCacheItem>();
		items.add(new SVDBDeclCacheItem(null, "my_filename", "item", SVDBItemType.ActionBlockStmt, false));
		cd.getDeclCacheMap().put("foobar", items);
		
		start = System.currentTimeMillis();		
		for (int i=0; i<iter; i++) {
			writer.init(dout);
			
//			for (String file : files) {
				writer.writeObject(SVDBBaseIndexCacheData.class, cd);
				writer.writeObject(SVDBArgFileIndexCacheData.class, acd);
				writer.writeObject(SVDBFile.class, f);
				total++;
//			}
		}
		total=0;

		din = new DataInputStream(new ByteArrayInputStream(bos.toByteArray()));
		for (int i=0; i<iter; i++) {
			reader.init(din);
			
//			for (String file : files) {
				reader.readObject(null, SVDBBaseIndexCacheData.class, cd2);
				reader.readObject(null, SVDBArgFileIndexCacheData.class, acd2);
				reader.readObject(null, SVDBFile.class, f2);
				total++;
//			}
		}
		end = System.currentTimeMillis();
		total_time = (end-start);
		
		System.out.println("f2.path=" + f2.getFilePath());
		
		if (total_time == 0) {
			total_time=1;
		}

		System.out.println("Performance: " + total + " items in " + total_time + "ms");
		System.out.println("    " + (total_time/total) + " ms/item");

		LogFactory.removeLogHandle(log);
	}
}
