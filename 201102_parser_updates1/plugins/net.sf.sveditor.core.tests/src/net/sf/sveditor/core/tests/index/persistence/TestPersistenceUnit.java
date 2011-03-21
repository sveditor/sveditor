package net.sf.sveditor.core.tests.index.persistence;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.DBWriteException;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceWriter;
import net.sf.sveditor.core.scanner.SVPreProcScanner;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

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
		rgy.init((File)null);

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
	
}
