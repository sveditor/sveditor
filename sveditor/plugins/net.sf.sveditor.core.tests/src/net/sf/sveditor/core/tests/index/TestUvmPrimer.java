/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package net.sf.sveditor.core.tests.index;

import java.io.File;

import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;

public class TestUvmPrimer extends SVCoreTestCaseBase {
	
	
	public void test_03_Interfaces_and_BFMs() {
		SVCorePlugin.getDefault().enableDebug(false);

		runTest(getName(), "03_Interfaces_and_BFMs");
	}
	
	public void test_10_An_Object_Oriented_Testbench() {
		SVCorePlugin.getDefault().enableDebug(false);

		runTest(getName(), "10_An_Object_Oriented_Testbench");
	}
	
	public void test_11_UVM_Test() {
		SVCorePlugin.getDefault().enableDebug(false);

		runTest(getName(), "11_UVM_Test");
	}
	
	private void runTest(String name, String path) {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
	
		File pdir = new File(fTmpDir, path);
		assertTrue(pdir.mkdirs());
		
		utils.unpackBundleZipToFS("uvmprimer-master.zip", pdir);
		
		utils.unpackBundleZipToFS("uvm.zip", pdir);
		
		File filelist = new File(pdir, "filelist.f");
		
		SVFileUtils.copy(
				"+define+QUESTA\n" +
				"+incdir+./uvm/src\n" +
				"./uvm/src/uvm_pkg.sv\n" +
				"+incdir+./uvmprimer-master/" + path + "\n" +
				"-F uvmprimer-master/" + path + "/rtl.f\n" +
				"-F uvmprimer-master/" + path + "/tb.f\n",
				filelist);
		
		ISVDBIndex index = 
			fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
					filelist.toString(), SVDBArgFileIndexFactory.TYPE, null);
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
		
	}
	

//			
//	protected void doTestUVMExample(String 			testName, 
//								 File 				testDir, 
//								 File 				projDir, 
//								 String 			listFileContent, 
//								 HashSet<String> 	requiredClasses,
//								 HashMap<String,HashSet<String>> requiredPkgDecls) {
//		
//		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
//		
//		if(requiredClasses != null) {
//			requiredClasses.add("uvm_component") ;
//			requiredClasses.add("uvm_sequence") ;
//			requiredClasses.add("uvm_object") ;
//			requiredClasses.add("uvm_sequencer") ;
//			requiredClasses.add("uvm_agent") ;
//			requiredClasses.add("uvm_transaction") ;
//		} else {
//			requiredClasses = new HashSet<String>();
//		}
//		
//		testDir.mkdirs();
//		
//		utils.unpackBundleZipToFS("/uvm.zip", testDir);		
//		
//		File listFile = new File(projDir, "file.list") ;
//		
//		IProject project = TestUtils.createProject(testName, projDir) ;
//		addProject(project);
//		
//		SVFileUtils.writeToFile(listFile, listFileContent) ;
//		
//		ISVDBIndex index = 
//			fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
//				listFile.toString(),
//				SVDBArgFileIndexFactory.TYPE, null);
//		index.loadIndex(new NullProgressMonitor());
//		
//		List<SVDBDeclCacheItem> items = SVDBFindDeclOp.op(index, "", 
//				new ISVDBFindNameMatcher() {
//					public boolean match(ISVDBNamedItem it, String name) {
//						return true;
//					}
//				}, true);
//		
//		for (SVDBDeclCacheItem it : items) {
//			if (!it.isFileTreeItem()) {
//				assertNotNull("Cache Item: " + it.getName() + " is null", it.getSVDBItem());
//			}
//		}
//		
//		for (SVDBDeclCacheItem it : items) {
//			if (it.isFileTreeItem()) {
////				System.out.println("it=" + it.getName() + " file=" + it.getFilename());
//				if (it.getSVDBItem() == null) {
//					for (String path : index.getFileList(new NullProgressMonitor())) {
//						System.out.println("  path=" + path);
//					}
//					assertNotNull("Cache Item: " + it.getName() + " is null", it.getSVDBItem());
//				}
//				assertNotNull("Cache Item: " + it.getName() + " is null", it.getSVDBItem());
//			}
//		}
//		
//		/*
//		while (it.hasNext()) {
//			ISVDBItemBase item = it.nextItem();
//			if (item.getType() == SVDBItemType.Marker) {
//				SVDBMarker m = (SVDBMarker)item ;
//				if (m.getMarkerType() == MarkerType.Error) {
//					errors.add(m);
//				}
//			} else if (item.getType() == SVDBItemType.ClassDecl) {
//				String itemName = SVDBItem.getName(item) ;
//				if(requiredClasses != null && requiredClasses.contains(itemName)) {
//					requiredClasses.remove(itemName) ;
//				}
//			} else if (SVDBStmt.isType(item, SVDBItemType.VarDeclStmt)) {
//				SVDBVarDeclStmt v = (SVDBVarDeclStmt)item;
//				SVDBVarDeclItem vi = (SVDBVarDeclItem)v.getChildren().iterator().next();
//				assertNotNull("Variable " + SVDBItem.getName(v.getParent()) + "." +
//						vi.getName() + " has a null TypeInfo", v.getTypeInfo());
//			}
//		}
//	
//		if(requiredPkgDecls != null) {
//			for(String requiredPkgName: requiredPkgDecls.keySet()) {
//				log.debug("Searching for required package: " + requiredPkgName);
//				
//				List<SVDBDeclCacheItem> packages = index.findGlobalScopeDecl(new NullProgressMonitor(), "packages", new SVDBFindPackageMatcher()) ;
//			
//				// Hash up the pkgs by name
//				HashMap<String,SVDBDeclCacheItem> pkgMap = new HashMap<String,SVDBDeclCacheItem>() ;
//				log.debug("--> List of Packages");
//				for(SVDBDeclCacheItem pkg: packages) {
//					log.debug("  Package: " + pkg.getName());
//					pkgMap.put(pkg.getName(), pkg) ;
//				}
//				log.debug("<-- List of Packages");
//
//				assertTrue("Package " + requiredPkgName + " does not exist",
//						pkgMap.containsKey(requiredPkgName));
//				if(pkgMap.containsKey(requiredPkgName)) {
//					// Fetch all the packages content from the decl cache
//					List<SVDBDeclCacheItem> pkgDecls = index.findPackageDecl(new NullProgressMonitor(), pkgMap.get(requiredPkgName)); 
//					
//					assertNotNull("findPackageDecl returns null", pkgDecls);
//					if(pkgDecls != null) {
//						// Hash up all the pkg decls by name
//						HashMap<String, SVDBDeclCacheItem> pkgDeclMap = new HashMap<String,SVDBDeclCacheItem>() ;
//						log.debug("--> Content of package " + requiredPkgName);
//						for(SVDBDeclCacheItem decl: pkgDecls) {
//							log.debug("  Item: " + decl.getType() + " " + decl.getName());
//							pkgDeclMap.put(decl.getName(), decl) ;
//						}
//						log.debug("<-- Content of package " + requiredPkgName);
//						// Copy the required decl map so we can itterated over the copy while deleting from the original
//						HashSet<String> requiredPkgDeclsCopy = new HashSet<String>(requiredPkgDecls.get(requiredPkgName)) ;
//						// Search the map for all required package decls
//						for(String requiredPkgDecl: requiredPkgDeclsCopy) {
//							if(pkgDeclMap.containsKey(requiredPkgDecl)) {
//								requiredPkgDecls.get(requiredPkgName).remove(requiredPkgDecl) ;
//							}
//						}
//					}
//				}
//			}
//		}
//		 */
//		
//		IndexTestUtils.assertNoErrWarn(fLog, index);
//		IndexTestUtils.assertFileHasElements(fLog, index, 
//				requiredClasses.toArray(new String[requiredClasses.size()]));
//
//		/*
//		if(requiredClasses != null) {
//			for(String className : requiredClasses) {
//				log.error("[ERROR] " + "Class \"" + className + "\" not found") ;
//			}
//			assertTrue("Not all expected classes were parsed", requiredClasses.size()==0) ;
//		}
//		
//		int unfoundDecls = 0 ;
//		if(requiredPkgDecls != null) {
//			for(String pkgName: requiredPkgDecls.keySet()) {
//				for(String declName: requiredPkgDecls.get(pkgName)) {
//					log.error("[ERROR] " + "Pkg decl \"" + pkgName + "::" + declName + "\" not found") ;
//					unfoundDecls++ ;
//				}
//			}
//		}
//		assertEquals("Not all package decls found",0, unfoundDecls) ;
//		
//		
//		LogFactory.removeLogHandle(log);
//		 */
//	}

}
