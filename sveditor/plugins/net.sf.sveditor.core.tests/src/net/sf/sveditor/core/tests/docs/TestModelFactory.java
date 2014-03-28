/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/

package net.sf.sveditor.core.tests.docs;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.nio.charset.Charset;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.search.SVDBFindPackageMatcher;
import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.model.DocModel;
import net.sf.sveditor.core.docs.model.DocModelFactory;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

import difflib.Delta;
import difflib.DiffUtils;
import difflib.Patch;

public class TestModelFactory extends SVCoreTestCaseBase {
	
	boolean fDebug 			= false ;
	
	
	
	
	@Override
	protected void tearDown() throws Exception {
		// TODO Auto-generated method stub
		super.tearDown();
	}
	/*
	 */

	public void testUVM() throws IOException {
		
		fDebug = true ;
		
		String test_name = "testBasicExamplePkg" ;
		String bundle_dir_name = "basic_uvm" ;
		String test_bundle_dir = "/data/doc_gen/" + bundle_dir_name ;
		
		SVCorePlugin.getDefault().enableDebug(false);
		
		doTestUVMExample(
				test_name, 
				bundle_dir_name,
				test_bundle_dir) ;

	}			
	
	public void doTestUVMExample(
			String 			testName, 
			String			bundleDirName,
			String			testBundleDir) throws IOException {

		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		LogHandle log = LogFactory.getLogHandle(testName);
		
		File testDir  		= new File(fTmpDir,  testName) ;
		File projDir  		= testDir ;
		File cpBundleDir 	= new File(testDir, bundleDirName) ;
		File listFile  		= new File(cpBundleDir, "file.list") ;

		testDir.mkdirs() ;
		
		fLog.debug(ILogLevel.LEVEL_OFF, "+-----------------------------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_OFF, "| testName ........ " + testName ) ;
		fLog.debug(ILogLevel.LEVEL_OFF, "| testBundleDir ... " + testBundleDir ) ;
		fLog.debug(ILogLevel.LEVEL_OFF, "| testDir ......... " + testDir.getPath() ) ;
		fLog.debug(ILogLevel.LEVEL_OFF, "| cpBundleDir ..... " + cpBundleDir.getPath() ) ;
		fLog.debug(ILogLevel.LEVEL_OFF, "| projDir ......... " + projDir.getPath() ) ;
		fLog.debug(ILogLevel.LEVEL_OFF, "| listFIle ........ " + listFile.getPath() ) ;
		fLog.debug(ILogLevel.LEVEL_OFF, "+-----------------------------------------------------------") ;
		
		IProject project = TestUtils.createProject(testName, projDir) ;
		addProject(project);
		utils.unpackBundleZipToFS("/uvm.zip", testDir);		
		utils.copyBundleDirToWS(testBundleDir, project) ;

		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
						listFile.toString(),
						SVDBArgFileIndexFactory.TYPE, null);
		
		index.loadIndex(new NullProgressMonitor()) ;
		
		/*
		 * Select all index packages for document generation by
		 * querying the global decl cache for all package decls and
		 * adding them to the DocGenConfig
		 */
		
		DocGenConfig cfg = new DocGenConfig() ;
		
		Map<SVDBDeclCacheItem,Tuple<SVDBDeclCacheItem, ISVDBIndex>> pkgMap = 
				new HashMap<SVDBDeclCacheItem, Tuple<SVDBDeclCacheItem,ISVDBIndex>>() ;
	
		List<ISVDBIndex> projIndexList = fIndexRgy.getAllProjectLists() ;
		for(ISVDBIndex svdbIndex: projIndexList) {
			List<SVDBDeclCacheItem> foundPkgs = svdbIndex.findGlobalScopeDecl(new NullProgressMonitor(),"pkgs",new SVDBFindPackageMatcher()) ;
			for(SVDBDeclCacheItem pkg: foundPkgs) {
				if(!pkgMap.containsKey(pkg.getName())) { 
					pkgMap.put(
							pkg,
							new Tuple<SVDBDeclCacheItem,ISVDBIndex>(pkg,svdbIndex)) ; 
				}
			}
		}		
		
//		Set<Tuple<SVDBDeclCacheItem,ISVDBIndex>> pkgs = new HashSet<Tuple<SVDBDeclCacheItem,ISVDBIndex>>(pkgMap.values()) ;
		
//        Map<SVDBDeclCacheItem, Tuple<SVDBDeclCacheItem, ISVDBIndex>> pkgs = new HashMap<SVDBDeclCacheItem, Tuple<SVDBDeclCacheItem, ISVDBIndex>>() ;
		
		
//		cfg.setSelectedPackages(pkgs) ;
		cfg.setPkgSet(pkgMap);
		
		//
		//
		//
		
//		SVCorePlugin.getDefault().enableDebug(fDebug) ;
		
		DocModelFactory factory = new DocModelFactory() ;
		DocModel model = factory.build(cfg) ;
		
		File modelDumpPathAct = new File(testDir, "model_dump_act.txt") ;
		File modelDumpPathExp = new File(cpBundleDir, "model_dump_exp.txt") ;
		
		OutputStreamWriter fw = new OutputStreamWriter(new FileOutputStream(modelDumpPathAct.getPath()), Charset.forName("UTF-8") ) ;
		BufferedWriter bw = new BufferedWriter(fw) ;
		model.dumpToFile(bw) ;
		bw.close() ;
		fw.close() ;

		List<String> expLines = TestUtils.fileToLines(modelDumpPathExp.getPath()) ;
		List<String> actLines = TestUtils.fileToLines(modelDumpPathAct.getPath()) ;

		Patch patch = DiffUtils.diff(expLines, actLines) ;

		List<Delta> deltas = patch.getDeltas() ;
		
		if(deltas.size() != 0) {
                        fLog.debug(ILogLevel.LEVEL_OFF, "+--------------------------------------------------------------------") ;
                        fLog.debug(ILogLevel.LEVEL_OFF, "| To debug, rerun test with fDebug==true then diff the dumps below") ;
                        fLog.debug(ILogLevel.LEVEL_OFF, "+--------------------------------------------------------------------") ;
                        fLog.debug(ILogLevel.LEVEL_OFF, "| modelDumpPathAct: " + modelDumpPathAct ) ;
                        fLog.debug(ILogLevel.LEVEL_OFF, "| modelDumpPathExp: " + modelDumpPathExp ) ;
                        fLog.debug(ILogLevel.LEVEL_OFF, "| >>   diff " + modelDumpPathExp + " " + modelDumpPathAct ) ;
                        fLog.debug(ILogLevel.LEVEL_OFF, "| >> tkdiff " + modelDumpPathExp + " " + modelDumpPathAct ) ;
                        fLog.debug(ILogLevel.LEVEL_OFF, "| +--------------------------------------------------------------------") ;
                        fLog.debug(ILogLevel.LEVEL_OFF, "| | If the differences are expected, check them in as golden") ;
                        fLog.debug(ILogLevel.LEVEL_OFF, "| +--------------------------------------------------------------------") ;
                        fLog.debug(ILogLevel.LEVEL_OFF, "| | <from-your-repo-root> cp " + modelDumpPathAct + " "
                                                                                                                + "sveditor/plugins/net.sf.sveditor.core.tests" 
                                                                                                                + testBundleDir 
                                                                                                                + "/model_dump_exp.txt") ;
                        fLog.debug(ILogLevel.LEVEL_OFF, "| +--------------------------------------------------------------------") ;
                        fLog.debug(ILogLevel.LEVEL_OFF, "+--------------------------------------------------------------------") ;
		}
		

		assertTrue( 
				String.format("Detected %d deltas against expected model dump.\n\tExp:%s\n\tAct:%s\n",
						deltas.size(),
						modelDumpPathExp.toString(),
						modelDumpPathAct.toString()),
						deltas.size()==0) ;

		//
		//
		//

		LogFactory.removeLogHandle(log);
	}	
	
	

}
