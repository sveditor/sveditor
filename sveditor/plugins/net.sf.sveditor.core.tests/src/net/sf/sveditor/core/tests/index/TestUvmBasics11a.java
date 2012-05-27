/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.index;

import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.stmt.SVDBStmt;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclItem;
import net.sf.sveditor.core.db.stmt.SVDBVarDeclStmt;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestUvmBasics11a extends TestCase {
	
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
			TestUtils.delete(fTmpDir);
		}
	}
	
	public void testBasicExamplePkg() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = "testBasicExamplePkg" ;
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm-1.1a/examples/simple/basic_examples/pkg") ;
		File uvm_dir   = new File(test_dir, "uvm-1.1a") ;
		File uvm_pkg   = new File(test_dir, "uvm-1.1a/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append("+incdir+"+uvm_dir.toString()+"/src\n" +
								uvm_pkg.toString()+"\n" +
		                        "test.sv\n") ;		
		
		HashSet<String> requiredClasses = TestUtils.newHashSet("lower",
				                                               "myunit",
				                                               "myunit_wrapper",
				                                               "mydata_wrapper") ;
		
		doTestUVMExample(test_name, 
				test_dir, 
				proj_dir, 
				list_file_conent.toString(),
				requiredClasses ) ;

	}	
	
	public void testBasicExampleEventPool() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = "testBasicExampleEventPool" ;
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm-1.1a/examples/simple/basic_examples/event_pool") ;
		File uvm_dir   = new File(test_dir, "uvm-1.1a") ;
		File uvm_pkg   = new File(test_dir, "uvm-1.1a/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append("+incdir+"+uvm_dir.toString()+"/src\n" +
								uvm_pkg.toString()+"\n" +
		                        "test.sv\n") ;		
		
		HashSet<String> requiredClasses = TestUtils.newHashSet() ;
		
		doTestUVMExample(test_name, 
				test_dir, 
				proj_dir, 
				list_file_conent.toString(),
				requiredClasses ) ;


	}	
	
	public void testBasicExampleModule() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = "testBasicExampleModule" ;
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm-1.1a/examples/simple/basic_examples/module") ;
		File uvm_dir   = new File(test_dir, "uvm-1.1a") ;
		File uvm_pkg   = new File(test_dir, "uvm-1.1a/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append("+incdir+"+uvm_dir.toString()+"/src\n" +
								uvm_pkg.toString()+"\n" +
		                        "test.sv\n") ;		
		
		HashSet<String> requiredClasses = TestUtils.newHashSet("lower","mydata") ;
		
		doTestUVMExample(test_name, 
				test_dir, 
				proj_dir, 
				list_file_conent.toString(),
				requiredClasses ) ;


	}	
	
	public void testTrivial() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = "testTrivial" ;
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm-1.1a/examples/simple/trivial") ;
		File uvm_dir   = new File(test_dir, "uvm-1.1a") ;
		File uvm_pkg   = new File(test_dir, "uvm-1.1a/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append("+incdir+"+uvm_dir.toString()+"/src\n" +
								uvm_pkg.toString()+"\n" +
		                        "component.sv\n") ;		
		
		HashSet<String> requiredClasses = TestUtils.newHashSet("my_component") ;
		
		doTestUVMExample(test_name, 
				test_dir, 
				proj_dir, 
				list_file_conent.toString(),
				requiredClasses ) ;


	}				
	
	public void testSequenceBasicReadWrite() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = "testSequenceBasicReadWrite" ;
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm-1.1a/examples/simple/sequence/basic_read_write_sequence") ;
		File uvm_dir   = new File(test_dir, "uvm-1.1a") ;
		File uvm_pkg   = new File(test_dir, "uvm-1.1a/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append("+incdir+"+uvm_dir.toString()+"/src\n" +
								uvm_pkg.toString()+"\n" +
		                        "top.sv\n") ;		
		
		HashSet<String> requiredClasses = TestUtils.newHashSet("bus_trans", "bus_rsp", "bus_req", "my_driver", "sequenceA", "env") ;
		
		doTestUVMExample(test_name, 
				test_dir, 
				proj_dir, 
				list_file_conent.toString(),
				requiredClasses ) ;

	}				
	
	public void testInterfaces() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = "testInterfaces" ;
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm-1.1a/examples/simple/interfaces") ;
		File uvm_dir   = new File(test_dir, "uvm-1.1a") ;
		File uvm_pkg   = new File(test_dir, "uvm-1.1a/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append("+incdir+"+uvm_dir.toString()+"/src\n" +
								uvm_pkg.toString()+"\n" +
		                        "interface.sv\n") ;		
		
		HashSet<String> requiredClasses = TestUtils.newHashSet("driver", "env") ;
		
		doTestUVMExample(test_name, 
				test_dir, 
				proj_dir, 
				list_file_conent.toString(),
				requiredClasses ) ;

	}				
			
	public void doTestUVMExample(String 			testName, 
								 File 				testDir, 
								 File 				projDir, 
								 String 			listFileContent, 
								 HashSet<String> 	requiredClasses) {
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(testName);
		
		requiredClasses.add("uvm_component") ;
		requiredClasses.add("uvm_sequence") ;
		requiredClasses.add("uvm_object") ;
		requiredClasses.add("uvm_sequencer") ;
		requiredClasses.add("uvm_agent") ;
		requiredClasses.add("uvm_transaction") ;
		
		testDir.mkdirs();
		
		utils.unpackBundleZipToFS("/uvm-1.1a.zip", testDir);		
		
		File listFile = new File(projDir, "file.list") ;
		
		IProject project = TestUtils.createProject(testName, projDir) ;
		
		SVFileUtils.writeToFile(listFile, listFileContent) ;
		
		File db = new File(fTmpDir, "db");
		if (db.exists()) {
			db.delete();
		}
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(TestIndexCacheFactory.instance(db));
		
		ISVDBIndex index = 
			rgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				listFile.toString(),
				SVDBArgFileIndexFactory.TYPE, null);
		
		ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> errors = new ArrayList<SVDBMarker>();
		
		while (it.hasNext()) {
			ISVDBItemBase item = it.nextItem();
			if (item.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)item ;
				if (m.getMarkerType() == MarkerType.Error) {
					errors.add(m);
				}
			} else if (item.getType() == SVDBItemType.ClassDecl) {
				String itemName = SVDBItem.getName(item) ;
				if(requiredClasses.contains(itemName)) {
					requiredClasses.remove(itemName) ;
				}
			} else if (SVDBStmt.isType(item, SVDBItemType.VarDeclStmt)) {
				SVDBVarDeclStmt v = (SVDBVarDeclStmt)item;
				SVDBVarDeclItem vi = (SVDBVarDeclItem)v.getChildren().iterator().next();
				assertNotNull("Variable " + SVDBItem.getName(v.getParent()) + "." +
						vi.getName() + " has a null TypeInfo", v.getTypeInfo());
			}
		}
		
		for (SVDBMarker m : errors) {
			log.error("[ERROR] " + m.getMessage());
		}
		
		assertEquals("Check that no errors were found", 0, errors.size());
		
		for(String className : requiredClasses) {
			log.error("[ERROR] " + "Class \"" + className + "\" not found") ;
		}
		
		assertTrue("Not all expected classes were parsed", requiredClasses.size()==0) ;
		
		for (SVDBMarker m : errors) {
			log.error("[ERROR] " + m.getMessage());
		}
		assertEquals("No errors", 0, errors.size());
		
		LogFactory.removeLogHandle(log);
		TestUtils.deleteProject(project);		
	}

}
