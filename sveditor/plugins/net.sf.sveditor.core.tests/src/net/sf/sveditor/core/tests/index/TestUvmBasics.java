/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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
import java.io.IOException;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.ISVDBNamedItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexInt;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexStats;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.ops.SVDBFindDeclOp;
import net.sf.sveditor.core.db.refs.SVDBFileRefCollector;
import net.sf.sveditor.core.db.search.ISVDBFindNameMatcher;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.preproc.ISVPreProcessor;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestUvmBasics extends SVCoreTestCaseBase {
	
	public void testBasicExamplePkg() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = getName();
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm/examples/simple/basic_examples/pkg") ;
		File uvm_dir   = new File(test_dir, "uvm") ;
		File uvm_pkg   = new File(test_dir, "uvm/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append("+define+QUESTA\n");
		list_file_conent.append(
				"+incdir+"+uvm_dir.toString()+"/src\n" +
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
				requiredClasses,
				null) ;

	}	
	
	public void testBasicExampleEventPool() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = "testBasicExampleEventPool" ;
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm/examples/simple/basic_examples/event_pool") ;
		File uvm_dir   = new File(test_dir, "uvm") ;
		File uvm_pkg   = new File(test_dir, "uvm/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append("+define+QUESTA\n");
		list_file_conent.append("+incdir+"+uvm_dir.toString()+"/src\n" +
								uvm_pkg.toString()+"\n" +
		                        "test.sv\n") ;		
		
		HashSet<String> requiredClasses = TestUtils.newHashSet() ;
		
		doTestUVMExample(test_name, 
				test_dir, 
				proj_dir, 
				list_file_conent.toString(),
				requiredClasses,
				null) ;


	}	
	
	public void testBasicExampleModule() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = "testBasicExampleModule" ;
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm/examples/simple/basic_examples/module") ;
		File uvm_dir   = new File(test_dir, "uvm") ;
		File uvm_pkg   = new File(test_dir, "uvm/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append("+define+QUESTA\n");
		list_file_conent.append("+incdir+"+uvm_dir.toString()+"/src\n" +
								uvm_pkg.toString()+"\n" +
		                        "test.sv\n") ;		
		
		HashSet<String> requiredClasses = TestUtils.newHashSet("lower","mydata") ;
		
		doTestUVMExample(test_name, 
				test_dir, 
				proj_dir, 
				list_file_conent.toString(),
				requiredClasses,
				null) ;


	}	
	
	public void testTrivial() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = "testTrivial" ;
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm/examples/simple/trivial") ;
		File uvm_dir   = new File(test_dir, "uvm") ;
		File uvm_pkg   = new File(test_dir, "uvm/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append(
				"+define+QUESTA\n" +
				"+incdir+"+uvm_dir.toString()+"/src\n" +
								uvm_pkg.toString()+"\n" +
		                        "component.sv\n") ;		
		
		HashSet<String> requiredClasses = TestUtils.newHashSet("my_component") ;
		
		doTestUVMExample(test_name, 
				test_dir, 
				proj_dir, 
				list_file_conent.toString(),
				requiredClasses,
				null) ;


	}				
	
	public void testSequenceBasicReadWrite() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = "testSequenceBasicReadWrite" ;
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm/examples/simple/sequence/basic_read_write_sequence") ;
		File uvm_dir   = new File(test_dir, "uvm") ;
		File uvm_pkg   = new File(test_dir, "uvm/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append("+define+QUESTA\n");
		list_file_conent.append("+incdir+"+uvm_dir.toString()+"/src\n" +
								uvm_pkg.toString()+"\n" +
		                        "top.sv\n") ;		
		
		HashSet<String> requiredClasses = TestUtils.newHashSet("bus_trans", "bus_rsp", "bus_req", "my_driver", "sequenceA", "env") ;
		
		doTestUVMExample(test_name, 
				test_dir, 
				proj_dir, 
				list_file_conent.toString(),
				requiredClasses,
				null) ;

	}				
	
	public void testSequenceBasicReadWriteWithDeclCache() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = "testSequenceBasicReadWrite" ;
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm/examples/simple/sequence/basic_read_write_sequence") ;
		File uvm_dir   = new File(test_dir, "uvm") ;
		File uvm_pkg   = new File(test_dir, "uvm/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append("+define+QUESTA\n");
		list_file_conent.append("+incdir+"+uvm_dir.toString()+"/src\n" +
								uvm_pkg.toString()+"\n" +
		                        "top.sv\n") ;		
		
		HashMap<String,HashSet<String>> requiredPkgDecls = new HashMap<String,HashSet<String>>() ;
		
		requiredPkgDecls.put("user_pkg", 
				TestUtils.newHashSet("bus_trans", "bus_rsp", "bus_req", "my_driver", "sequenceA", "env")) ;
		requiredPkgDecls.put("uvm_pkg", 
				TestUtils.newHashSet("uvm_component","uvm_sequence","uvm_object","uvm_sequencer","uvm_agent","uvm_transaction")) ;
		
		doTestUVMExample(test_name, 
				test_dir, 
				proj_dir, 
				list_file_conent.toString(),
				null,
				requiredPkgDecls) ;

	}		
	public void testInterfaces() {
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		String test_name = "testInterfaces" ;
		
		File test_dir  = new File(fTmpDir,  test_name) ;
		File proj_dir  = new File(test_dir, "uvm/examples/simple/interfaces") ;
		File uvm_dir   = new File(test_dir, "uvm") ;
		File uvm_pkg   = new File(test_dir, "uvm/src/uvm_pkg.sv") ;
		
		StringBuilder list_file_conent = new StringBuilder();
		
		list_file_conent.append("+define+QUESTA\n");
		list_file_conent.append("+incdir+"+uvm_dir.toString()+"/src\n" +
								uvm_pkg.toString()+"\n" +
		                        "interface.sv\n") ;		
		
		HashSet<String> requiredClasses = TestUtils.newHashSet("driver", "env") ;
		
		doTestUVMExample(test_name, 
				test_dir, 
				proj_dir, 
				list_file_conent.toString(),
				requiredClasses,
				null) ;

	}				

	public void testUVMIncludeRefs() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle("testXbusExample");
		
		File test_dir = new File(fTmpDir, "testXbusExample");
		assertTrue(test_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/uvm.zip", test_dir);		
		File uvm_src = new File(test_dir, "uvm/src");
		
		PrintStream ps = new PrintStream(new File(uvm_src, "uvm.f"));
		ps.println("+incdir+.");
		ps.println("uvm_pkg.sv");
		ps.close();
		
		IProject project = TestUtils.createProject("uvm", uvm_src);
		addProject(project);
		
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/uvm/uvm.f", SVDBArgFileIndexFactory.TYPE, null);
		index.init(new NullProgressMonitor(), null);
		index.setGlobalDefine("QUESTA", "");
		
		index.loadIndex(new NullProgressMonitor());
		
		
		IndexTestUtils.assertNoErrWarn(log, index);
		
		for (String filename : index.getFileList(new NullProgressMonitor())) {
			SVDBFileRefCollector finder = new SVDBFileRefCollector();
			SVDBFile file = index.findFile(filename);
			fLog.debug("[VISIT FILE] " + filename);
// MSB:
//			finder.visitFile(file);
			Map<String, List<Integer>> ref = finder.getReferences();
	
			/*
			for (SVDBRefType t : SVDBRefType.values()) {
				System.out.println("    TYPE: " + t);
				for (String n : ref.getRefSet(t)) {
					System.out.println("        NAME: " + n);
				}
			}
			 */
		}
		
		LogFactory.removeLogHandle(log);
	}
	
	public void testParseUvmTLM2GenericPayload() throws IOException, CoreException {
		String testname = "testParseUvmTLM2GenericPayload";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
	
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		PrintStream ps;
		File pdir = new File(fTmpDir, testname);
		
		IProject project = TestUtils.createProject(testname, pdir);
		addProject(project);
		
		ps = new PrintStream(new File(pdir, testname + ".f"));
		ps.println("+incdir+../uvm/src");
		ps.println("+define+QUESTA");
//		ps.println("../uvm/src/uvm_pkg.sv");
		ps.println(testname + ".sv");
		ps.close();
		
		ps = new PrintStream(new File(pdir, testname + ".sv"));
		ps.println("`include \"uvm_macros.svh\"");
		ps.println("class " + testname + ";");
		ps.println("  function void do_record(uvm_recorder recorder);");
		ps.println("	if (!is_recording_enabled())");
		ps.println("		return;");
		ps.println("	super.do_record(recorder);");
		ps.println("	`uvm_record_field(\"address\",m_address)");
		ps.println("	MARKER_PRE = 1;");
		ps.println("	`uvm_record_field(\"command\",m_command.name())");
		ps.println("	MARKER_POST = 1;");
		ps.println("	`uvm_record_field(\"data_length\",m_length)");
		ps.println("	`uvm_record_field(\"byte_enable_length\",m_length)");
		ps.println("	`uvm_record_field(\"response_status\",m_response_status.name())");
		ps.println("	`uvm_record_field(\"streaming_width\",m_streaming_width)");
		ps.println("");
		ps.println("	for (int i=0; i < m_length; i++)");
		ps.println("		`uvm_record_field($sformatf(\"\\data[%0d] \", i), m_data[i])");
		ps.println("");
		ps.println("	for (int i=0; i < m_byte_enable_length; i++)");
		ps.println("		`uvm_record_field($sformatf(\"\\byte_en[%0d] \", i), m_byte_enable[i])");
		ps.println("");
		ps.println("	foreach (m_extensions[ext])");
		ps.println("		m_extensions[ext].record(recorder);");
		ps.println("	endfunction");
		ps.println("endclass");
		ps.close();

		// Ensure the project is up-to-date with new files
		project.refreshLocal(IResource.DEPTH_INFINITE, new NullProgressMonitor());

		ISVDBIndexInt index = (ISVDBIndexInt)fIndexRgy.findCreateIndex(
				new NullProgressMonitor(), testname + "_1", 
				"${workspace_loc}/" + testname + "/" + testname + ".f",
				SVDBArgFileIndexFactory.TYPE, null);
		
		index.loadIndex(new NullProgressMonitor());

		ISVPreProcessor pp = index.createPreProcScanner(
				"${workspace_loc}/" + testname + "/" + testname + ".sv");
		SVPreProcOutput pp_out = pp.preprocess();
		
		StringBuilder sb = new StringBuilder();
		int ch, lineno=1;
		
		while ((ch = pp_out.get_ch()) != -1) {
			
			if (ch == '\n') {
				log.debug(lineno + ": " + sb.toString());
				lineno++;
				sb.setLength(0);
			} else {
				sb.append((char)ch);
			}
		}
		if (sb.length() > 0) {
			log.debug(lineno + ": " + sb.toString());
		}
		
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(log, index);
	}
			
	protected void doTestUVMExample(String 			testName, 
								 File 				testDir, 
								 File 				projDir, 
								 String 			listFileContent, 
								 HashSet<String> 	requiredClasses,
								 HashMap<String,HashSet<String>> requiredPkgDecls) {
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		if(requiredClasses != null) {
			requiredClasses.add("uvm_component") ;
			requiredClasses.add("uvm_sequence") ;
			requiredClasses.add("uvm_object") ;
			requiredClasses.add("uvm_sequencer") ;
			requiredClasses.add("uvm_agent") ;
			requiredClasses.add("uvm_transaction") ;
		} else {
			requiredClasses = new HashSet<String>();
		}
		
		testDir.mkdirs();
		
		utils.unpackBundleZipToFS("/uvm.zip", testDir);		
		
		File listFile = new File(projDir, "file.list") ;
		
		IProject project = TestUtils.createProject(testName, projDir) ;
		addProject(project);
		
		SVFileUtils.writeToFile(listFile, listFileContent) ;
		
		ISVDBIndex index = 
			fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				listFile.toString(),
				SVDBArgFileIndexFactory.TYPE, null);
		index.loadIndex(new NullProgressMonitor());
		SVDBIndexStats stats = ((SVDBArgFileIndex)index).getIndexStats();
//		System.out.println("Stats:\n" + stats.toString());
		
		List<SVDBDeclCacheItem> items = SVDBFindDeclOp.op(index, "", 
				new ISVDBFindNameMatcher() {
					public boolean match(ISVDBNamedItem it, String name) {
						return true;
					}
				}, true);
		
		for (SVDBDeclCacheItem it : items) {
			if (!it.isFileTreeItem()) {
				assertNotNull("Cache Item: " + it.getName() + " (" + it.getType() + ") is null", it.getSVDBItem());
			}
		}

		for (SVDBDeclCacheItem it : items) {
			if (it.isFileTreeItem()) {
//				System.out.println("it=" + it.getName() + " file=" + it.getFilename());
				if (it.getSVDBItem() == null) {
					for (String path : index.getFileList(new NullProgressMonitor())) {
						System.out.println("  path=" + path);
					}
					assertNotNull("Cache Item: " + it.getName() + " is null", it.getSVDBItem());
				}
				assertNotNull("Cache Item: " + it.getName() + " is null", it.getSVDBItem());
			}
		}
		
		/*
		while (it.hasNext()) {
			ISVDBItemBase item = it.nextItem();
			if (item.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)item ;
				if (m.getMarkerType() == MarkerType.Error) {
					errors.add(m);
				}
			} else if (item.getType() == SVDBItemType.ClassDecl) {
				String itemName = SVDBItem.getName(item) ;
				if(requiredClasses != null && requiredClasses.contains(itemName)) {
					requiredClasses.remove(itemName) ;
				}
			} else if (SVDBStmt.isType(item, SVDBItemType.VarDeclStmt)) {
				SVDBVarDeclStmt v = (SVDBVarDeclStmt)item;
				SVDBVarDeclItem vi = (SVDBVarDeclItem)v.getChildren().iterator().next();
				assertNotNull("Variable " + SVDBItem.getName(v.getParent()) + "." +
						vi.getName() + " has a null TypeInfo", v.getTypeInfo());
			}
		}
	
		if(requiredPkgDecls != null) {
			for(String requiredPkgName: requiredPkgDecls.keySet()) {
				log.debug("Searching for required package: " + requiredPkgName);
				
				List<SVDBDeclCacheItem> packages = index.findGlobalScopeDecl(new NullProgressMonitor(), "packages", new SVDBFindPackageMatcher()) ;
			
				// Hash up the pkgs by name
				HashMap<String,SVDBDeclCacheItem> pkgMap = new HashMap<String,SVDBDeclCacheItem>() ;
				log.debug("--> List of Packages");
				for(SVDBDeclCacheItem pkg: packages) {
					log.debug("  Package: " + pkg.getName());
					pkgMap.put(pkg.getName(), pkg) ;
				}
				log.debug("<-- List of Packages");

				assertTrue("Package " + requiredPkgName + " does not exist",
						pkgMap.containsKey(requiredPkgName));
				if(pkgMap.containsKey(requiredPkgName)) {
					// Fetch all the packages content from the decl cache
					List<SVDBDeclCacheItem> pkgDecls = index.findPackageDecl(new NullProgressMonitor(), pkgMap.get(requiredPkgName)); 
					
					assertNotNull("findPackageDecl returns null", pkgDecls);
					if(pkgDecls != null) {
						// Hash up all the pkg decls by name
						HashMap<String, SVDBDeclCacheItem> pkgDeclMap = new HashMap<String,SVDBDeclCacheItem>() ;
						log.debug("--> Content of package " + requiredPkgName);
						for(SVDBDeclCacheItem decl: pkgDecls) {
							log.debug("  Item: " + decl.getType() + " " + decl.getName());
							pkgDeclMap.put(decl.getName(), decl) ;
						}
						log.debug("<-- Content of package " + requiredPkgName);
						// Copy the required decl map so we can itterated over the copy while deleting from the original
						HashSet<String> requiredPkgDeclsCopy = new HashSet<String>(requiredPkgDecls.get(requiredPkgName)) ;
						// Search the map for all required package decls
						for(String requiredPkgDecl: requiredPkgDeclsCopy) {
							if(pkgDeclMap.containsKey(requiredPkgDecl)) {
								requiredPkgDecls.get(requiredPkgName).remove(requiredPkgDecl) ;
							}
						}
					}
				}
			}
		}
		 */
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		IndexTestUtils.assertFileHasElements(fLog, index, 
				requiredClasses.toArray(new String[requiredClasses.size()]));

		/*
		if(requiredClasses != null) {
			for(String className : requiredClasses) {
				log.error("[ERROR] " + "Class \"" + className + "\" not found") ;
			}
			assertTrue("Not all expected classes were parsed", requiredClasses.size()==0) ;
		}
		
		int unfoundDecls = 0 ;
		if(requiredPkgDecls != null) {
			for(String pkgName: requiredPkgDecls.keySet()) {
				for(String declName: requiredPkgDecls.get(pkgName)) {
					log.error("[ERROR] " + "Pkg decl \"" + pkgName + "::" + declName + "\" not found") ;
					unfoundDecls++ ;
				}
			}
		}
		assertEquals("Not all package decls found",0, unfoundDecls) ;
		
		
		LogFactory.removeLogHandle(log);
		 */
	}

}
