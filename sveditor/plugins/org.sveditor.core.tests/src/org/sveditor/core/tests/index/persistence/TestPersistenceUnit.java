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


package org.sveditor.core.tests.index.persistence;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInput;
import java.io.DataInputStream;
import java.io.DataOutput;
import java.io.DataOutputStream;

import org.sveditor.core.SVCorePlugin;
import org.sveditor.core.db.index.SVDBBaseIndexCacheData;
import org.sveditor.core.db.persistence.DBFormatException;
import org.sveditor.core.db.persistence.DBWriteException;
import org.sveditor.core.db.persistence.IDBReader;
import org.sveditor.core.db.persistence.IDBWriter;
import org.sveditor.core.db.persistence.SVDBPersistenceRW;
import org.sveditor.core.db.refs.SVDBRefCacheEntry;
import org.sveditor.core.db.refs.SVDBRefType;

import junit.framework.TestCase;

public class TestPersistenceUnit extends TestCase {
	
	public void testRWRefCacheEntry() throws DBFormatException, DBWriteException {
		IDBWriter writer = new SVDBPersistenceRW();
		IDBReader reader = new SVDBPersistenceRW();
		SVDBRefCacheEntry entry = new SVDBRefCacheEntry();
		entry.setFilename("file1");
		entry.addTypeRef("type1");
	
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		DataOutput out = new DataOutputStream(bos); 
	
		writer.init(out);
		writer.writeObject(SVDBRefCacheEntry.class, entry);

		ByteArrayInputStream bin = new ByteArrayInputStream(bos.toByteArray());
		DataInput in = new DataInputStream(bin);
		reader.init(in);
	
		SVDBRefCacheEntry entry_i = new SVDBRefCacheEntry();
		reader.readObject(null, SVDBRefCacheEntry.class, entry_i);
	
//		assertEquals(entry.getFilename(), entry_i.getFilename());
		assertTrue(entry_i.getRefSet(SVDBRefType.TypeReference).contains("type1"));
	}
	
	public void testRWRefCacheEntryMap() throws DBFormatException, DBWriteException {
		SVCorePlugin.getDefault().enableDebug(false);
		IDBWriter writer = new SVDBPersistenceRW();
		IDBReader reader = new SVDBPersistenceRW();
		SVDBBaseIndexCacheData index_data = new SVDBBaseIndexCacheData("foo");
		SVDBRefCacheEntry entry = new SVDBRefCacheEntry();
		entry.setFilename("file1");
		entry.addTypeRef("type1");
//TODO:		index_data.fReferenceCacheMap.put("file1", entry);
	
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		DataOutput out = new DataOutputStream(bos); 
	
		writer.init(out);
		writer.writeObject(SVDBBaseIndexCacheData.class, index_data);

		ByteArrayInputStream bin = new ByteArrayInputStream(bos.toByteArray());
		DataInput in = new DataInputStream(bin);
		reader.init(in);

		SVDBBaseIndexCacheData index_data_i = new SVDBBaseIndexCacheData("");
		reader.readObject(null, SVDBBaseIndexCacheData.class, index_data_i);
		
	}
	
	/*
	// Ensures that each SVDBItemType has a corresponding class
	@SuppressWarnings("rawtypes")
	public void testItemsExist() {
		for (SVDBItemType type : SVDBItemType.values()) {
			ClassLoader cl = getClass().getClassLoader();
			String key = "SVDB" + type.name();
			Class cls = null;
			for (String pref : new String [] {"org.sveditor.core.db.", 
					"org.sveditor.core.db.stmt.",
			"org.sveditor.core.db.expr."}) {
				try {
					cls = cl.loadClass(pref + key);
				} catch (ClassNotFoundException e) { }
			}

			assertNotNull("Failed to locate class " + key, cls);
		}
	}

	// Ensures that each SVDBItemType has a corresponding class with 
	// a no-argument constructor
	@SuppressWarnings("rawtypes")
	public void testItemCtorExist() {
		for (SVDBItemType type : SVDBItemType.values()) {
			ClassLoader cl = getClass().getClassLoader();
			String key = "SVDB" + type.name();
			Class cls = null;
			for (String pref : new String [] {"org.sveditor.core.db.", 
					"org.sveditor.core.db.stmt.",
			"org.sveditor.core.db.expr."}) {
				try {
					cls = cl.loadClass(pref + key);
				} catch (ClassNotFoundException e) { }
			}

			assertNotNull("Failed to locate class " + key, cls);
		
			Object obj = null;
			try {
				obj = cls.newInstance();
			} catch (IllegalAccessException e) {
				fail("Failed to create instance of " + cls.getName() + ": " + e.getMessage());
			} catch (InstantiationException e) {
				fail("Failed to create instance of " + cls.getName() + ": " + e.getMessage());
			}
			
			assertNotNull("Failed to create class instanceof " + cls.getName(), obj);
		}
	}

	// Ensures that each SVDBItemType has a corresponding class with 
	// a no-argument constructor
	@SuppressWarnings("rawtypes")
	public void testItemDump() {
		SVDBPersistenceWriter writer = new SVDBPersistenceWriter(new ByteArrayOutputStream());
		
		for (SVDBItemType type : SVDBItemType.values()) {
			ClassLoader cl = getClass().getClassLoader();
			String key = "SVDB" + type.name();
			Class cls = null;
			for (String pref : new String [] {"org.sveditor.core.db.", 
					"org.sveditor.core.db.stmt.",
			"org.sveditor.core.db.expr."}) {
				try {
					cls = cl.loadClass(pref + key);
				} catch (ClassNotFoundException e) { }
			}

			assertNotNull("Failed to locate class " + key, cls);
		
			Object obj = null;
			try {
				obj = cls.newInstance();
			} catch (IllegalAccessException e) {
				fail("Failed to create instance of " + cls.getName() + ": " + e.getMessage());
			} catch (InstantiationException e) {
				fail("Failed to create instance of " + cls.getName() + ": " + e.getMessage());
			}
			
			assertNotNull("Failed to create class instanceof " + cls.getName(), obj);
			
			try {
				writer.writeSVDBItem((ISVDBItemBase)obj);
			} catch (DBWriteException e) {
				fail("Failed to write instance of " + cls.getName() + ": " + e.getMessage());
			}
		}
	}

	// Ensures that each SVDBItemType has a corresponding class with 
	// a no-argument constructor
	@SuppressWarnings("rawtypes")
	public void testItemDumpLoad() {
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		SVDBPersistenceWriter writer = new SVDBPersistenceWriter(bos);
		List<ISVDBItemBase> objects = new ArrayList<ISVDBItemBase>();
		List<ISVDBItemBase> result = null;
		
		for (SVDBItemType type : SVDBItemType.values()) {
			ClassLoader cl = getClass().getClassLoader();
			String key = "SVDB" + type.name();
			Class cls = null;
			for (String pref : new String [] {"org.sveditor.core.db.", 
					"org.sveditor.core.db.stmt.", "org.sveditor.core.db.expr."}) {
				try {
					cls = cl.loadClass(pref + key);
				} catch (ClassNotFoundException e) { }
			}

			assertNotNull("Failed to locate class " + key, cls);
		
			Object obj = null;
			try {
				obj = cls.newInstance();
			} catch (IllegalAccessException e) {
				fail("Failed to create instance of " + cls.getName() + ": " + e.getMessage());
			} catch (InstantiationException e) {
				fail("Failed to create instance of " + cls.getName() + ": " + e.getMessage());
			}
			
			assertNotNull("Failed to create class instanceof " + cls.getName(), obj);
			
			objects.add((ISVDBItemBase)obj);
		}
		
		try {
			writer.writeItemList(objects);
		} catch (DBWriteException e) {
			e.printStackTrace();
			fail("Failed to write item list: " + e.getMessage());
		}
		
		writer.close();
		SVDBPersistenceReader reader = new SVDBPersistenceReader(
				new ByteArrayInputStream(bos.toByteArray()));
				
		try {
			result = reader.readItemList(null);
		} catch (DBFormatException e) {
			e.printStackTrace();
			fail("Failed to read item list: " + e.getMessage());
		}
		
	}

	public void testOvmComponentParamUtilsExpansion() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		File tmp_dir = TestUtils.createTempDir();
		
		if (tmp_dir.exists()) {
			assertTrue(tmp_dir.delete());
		}
		assertTrue(tmp_dir.mkdirs());
		
		File db = new File(tmp_dir, "db");
		
		utils.unpackBundleZipToFS("/ovm.zip", tmp_dir);
		
		PrintStream ps = new PrintStream(new File(tmp_dir, "test.f"));
				
		ps.println("+incdir+./ovm/src");
		ps.println("./ovm/src/ovm_pkg.sv");
		ps.flush();
		ps.close();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(null));

		SVDBArgFileIndex index = (SVDBArgFileIndex)rgy.findCreateIndex(
				"GLOBAL", new File(tmp_dir, "test.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE, null);
		
		SVDBFile file = index.findFile("./ovm/src/methodology/ovm_random_stimulus.svh");
		
		assertNotNull(file);
		
		try {
			FileOutputStream fos = new FileOutputStream(new File(tmp_dir, "ovm_random_stimulus.bin"));
			SVDBPersistenceWriter writer = new SVDBPersistenceWriter(fos);
			
			System.out.println("--> writeSVDBItem");
			writer.writeSVDBItem(file);
			System.out.println("<-- writeSVDBItem");
			
			writer.close();
			fos.close();
			
			FileInputStream fin = new FileInputStream(new File(tmp_dir, "ovm_random_stimulus.bin"));
			SVDBPersistenceReader reader = new SVDBPersistenceReader(fin);
			
			System.out.println("--> readSVDBItem");
			ISVDBItemBase item = reader.readSVDBItem(null);
			System.out.println("<-- readSVDBItem");
		} catch (Exception e) {
			e.printStackTrace();
			fail("Caught exception: " + e.getMessage());
		}
	}
	 */
	
}
