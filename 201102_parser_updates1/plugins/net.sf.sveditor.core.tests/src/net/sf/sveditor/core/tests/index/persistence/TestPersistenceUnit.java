package net.sf.sveditor.core.tests.index.persistence;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceWriter;
import junit.framework.TestCase;

public class TestPersistenceUnit extends TestCase {
	
	// Ensures that each SVDBItemType has a corresponding class
	@SuppressWarnings("rawtypes")
	public void testItemsExist() {
		for (SVDBItemType type : SVDBItemType.values()) {
			ClassLoader cl = getClass().getClassLoader();
			String key = "SVDB" + type.name();
			Class cls = null;
			for (String pref : new String [] {"net.sf.sveditor.core.db.", 
					"net.sf.sveditor.core.db.stmt.",
			"net.sf.sveditor.core.db.expr."}) {
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
			for (String pref : new String [] {"net.sf.sveditor.core.db.", 
					"net.sf.sveditor.core.db.stmt.",
			"net.sf.sveditor.core.db.expr."}) {
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
			for (String pref : new String [] {"net.sf.sveditor.core.db.", 
					"net.sf.sveditor.core.db.stmt.",
			"net.sf.sveditor.core.db.expr."}) {
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
			for (String pref : new String [] {"net.sf.sveditor.core.db.", 
					"net.sf.sveditor.core.db.stmt.", "net.sf.sveditor.core.db.expr."}) {
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

}
