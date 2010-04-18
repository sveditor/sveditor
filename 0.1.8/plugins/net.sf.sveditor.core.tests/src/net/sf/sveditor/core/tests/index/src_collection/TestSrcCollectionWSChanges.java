package net.sf.sveditor.core.tests.index.src_collection;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexChangeListener;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBSourceCollectionIndexFactory;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.tests.Activator;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestSrcCollectionWSChanges extends TestCase 
	implements ISVDBIndexChangeListener {
	
	private int						fIndexRebuilt;
	private File					fTmpDir;

	@Override
	protected void setUp() throws Exception {
		System.out.println("setUp");
		super.setUp();
		
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		System.out.println("tearDown");
		super.tearDown();

		if (fTmpDir != null) {
			fTmpDir.delete();
			fTmpDir = null;
		}
	}

	public void testFileAdded() {
		fIndexRebuilt = 0;
		
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		IProject project_dir = TestUtils.createProject("project");

		utils.copyBundleDirToWS("/project_dir_src_collection_pkg/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db);
		SVCorePlugin.getDefault().getProjMgr().init();
		
		ISVDBIndex index = rgy.findCreateIndex("project", 
				"${workspace_loc}/project/project_dir_src_collection_pkg",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData p_data = p_mgr.getProjectData(project_dir);
		
		// Force the index to be rebuilt
		p_data.getProjectIndexMgr().getItemIterator();
		
//		assertEquals("Expecting index to be built once", 1, fIndexRebuilt);
		
		// Create a new class file
		String class_str = 
			"class class_1_2;\n" +
			"    function new();\n" +
			"    endfunction\n" +
			"endclass\n";
		
		IFile class_1_2_file = project_dir.getFile("/project_dir_src_collection_pkg/class_1_2.svh");
		try {
			
			class_1_2_file.create(new StringInputStream(class_str), 
					true, new NullProgressMonitor());
		} catch (CoreException e) {
			e.printStackTrace();
			fail("Exception while creating class: " + e.getMessage());
		}

		try {
			index.parse(class_1_2_file.getContents(), 
					"${workspace_loc}" + class_1_2_file.getFullPath());
		} catch (Exception e) {
			e.printStackTrace();
			fail("Failed to open class_1_2.svh: " + e.getMessage());
		}

		assertEquals("Expecting index to be built twice", 1, fIndexRebuilt);

		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem class1 = null;
		SVDBItem class2 = null;
		SVDBItem class3 = null;
		SVDBItem class_1_2 = null;
		SVDBItem def_function = null;
		List<SVDBItem> markers = new ArrayList<SVDBItem>();
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				class1 = tmp_it;
			} else if (tmp_it.getName().equals("class2")) {
				class2 = tmp_it;
			} else if (tmp_it.getName().equals("class3")) {
				class3 = tmp_it;
			} else if (tmp_it.getName().equals("def_function")) {
				def_function = tmp_it;
			} else if (tmp_it.getName().equals("class_1_2")) {
				class_1_2 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (SVDBItem warn : markers) {
			System.out.println("SVDBMarkerItem: " + 
					((SVDBMarkerItem)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertNotNull("located class_1_2", class_1_2);
		assertNotNull("located def_function", def_function);
		assertEquals("class1", class1.getName());
	}

	public void testFileRemoved() {
		fIndexRebuilt = 0;
		
		BundleUtils utils = new BundleUtils(Activator.getDefault().getBundle());
		IProject project_dir = TestUtils.createProject("project");

		utils.copyBundleDirToWS("/project_dir_src_collection_pkg/", project_dir);
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}

		// Create a new class file
		String class_str = 
			"class class_1_2;\n" +
			"    function new();\n" +
			"    endfunction\n" +
			"endclass\n";
		
		IFile class_1_2_file = project_dir.getFile("/project_dir_src_collection_pkg/class_1_2.svh");
		try {
			
			class_1_2_file.create(new StringInputStream(class_str), 
					true, new NullProgressMonitor());
		} catch (CoreException e) {
			e.printStackTrace();
			fail("Exception while creating class: " + e.getMessage());
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(db);
		SVCorePlugin.getDefault().getProjMgr().init();
		
		ISVDBIndex index = rgy.findCreateIndex("project", 
				"${workspace_loc}/project/project_dir_src_collection_pkg",
				SVDBSourceCollectionIndexFactory.TYPE, null);
		index.addChangeListener(this);
		SVDBProjectManager p_mgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData p_data = p_mgr.getProjectData(project_dir);
		
		// Force the index to be rebuilt
		p_data.getProjectIndexMgr().getItemIterator();
		
		try {
			index.parse(class_1_2_file.getContents(), 
					"${workspace_loc}" + class_1_2_file.getFullPath());
		} catch (Exception e) {
			e.printStackTrace();
			fail("Failed to open class_1_2.svh: " + e.getMessage());
		}

		ISVDBItemIterator<SVDBItem> it = index.getItemIterator();
		SVDBItem class1 = null;
		SVDBItem class2 = null;
		SVDBItem class3 = null;
		SVDBItem class_1_2 = null;
		SVDBItem def_function = null;
		List<SVDBItem> markers = new ArrayList<SVDBItem>();
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				class1 = tmp_it;
			} else if (tmp_it.getName().equals("class2")) {
				class2 = tmp_it;
			} else if (tmp_it.getName().equals("class3")) {
				class3 = tmp_it;
			} else if (tmp_it.getName().equals("def_function")) {
				def_function = tmp_it;
			} else if (tmp_it.getName().equals("class_1_2")) {
				class_1_2 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (SVDBItem warn : markers) {
			System.out.println("SVDBMarkerItem: " + 
					((SVDBMarkerItem)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertNotNull("located class_1_2", class_1_2);
		assertNotNull("located def_function", def_function);
		assertEquals("class1", class1.getName());
		
		// Now, remove the file
		try {
			class_1_2_file.delete(true, new NullProgressMonitor());
		} catch (CoreException e) {
			e.printStackTrace();
			fail("Failed to delete file: " + e.getMessage());
		}

		// Ask the index to parse the file even though it doesn't exist
		// The goal is to ensure that no exceptions are thrown
		SVDBFile class_1_2_db = null;
		try {
			class_1_2_db = index.parse(new StringInputStream(class_str), 
					"${workspace_loc}" + class_1_2_file.getFullPath());
		} catch (Exception e) {
			e.printStackTrace();
			fail("Failed to open class_1_2.svh: " + e.getMessage());
		}

		assertEquals("Expecting index to be built twice", 1, fIndexRebuilt);
		assertNull("class_1_2_db is not null", class_1_2_db);


		it = index.getItemIterator();
		class1 = null;
		class2 = null;
		class3 = null;
		class_1_2 = null;
		def_function = null;
		markers = new ArrayList<SVDBItem>();
		
		while (it.hasNext()) {
			SVDBItem tmp_it = it.nextItem();
			
			if (tmp_it.getName().equals("class1")) {
				class1 = tmp_it;
			} else if (tmp_it.getName().equals("class2")) {
				class2 = tmp_it;
			} else if (tmp_it.getName().equals("class3")) {
				class3 = tmp_it;
			} else if (tmp_it.getName().equals("def_function")) {
				def_function = tmp_it;
			} else if (tmp_it.getName().equals("class_1_2")) {
				class_1_2 = tmp_it;
			} else if (tmp_it.getType() == SVDBItemType.Marker) {
				markers.add(tmp_it);
			}
		}

		for (SVDBItem warn : markers) {
			System.out.println("SVDBMarkerItem: " + 
					((SVDBMarkerItem)warn).getMessage());
		}
		
		assertEquals("Confirm no warnings", 0, markers.size());
		assertNotNull("located class1", class1);
		assertNotNull("located class2", class2);
		assertNotNull("located class3", class3);
		assertNull("located class_1_2", class_1_2);
		assertNotNull("located def_function", def_function);
		assertEquals("class1", class1.getName());

	}

	// ISVDBIndexChangeListener implementation
	public void index_changed(int reason, SVDBFile file) {
	}

	public void index_rebuilt() {
		fIndexRebuilt++;
	}

}
