/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
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
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.search.SVDBFindPackageMatcher;
import net.sf.sveditor.core.docs.DocGenConfig;
import net.sf.sveditor.core.docs.model.DocModel;
import net.sf.sveditor.core.docs.model.DocModelFactory;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import difflib.*;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestModelFactory extends TestCase {
	
	boolean fDebug 			= false ;
	private LogHandle 		fLog ;
	private File			fTmpDir;
	private IProject		fProject;
	
	
	public TestModelFactory() {
		fLog = LogFactory.getLogHandle("TestParser") ;
	}
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		fTmpDir = TestUtils.createTempDir();
		fProject = null;
	}

	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.save_state();
	
		if (fProject != null && !fDebug) {
			TestUtils.deleteProject(fProject);
		}
		if (fTmpDir != null && fTmpDir.exists() &&!fDebug) {
			TestUtils.delete(fTmpDir);
		}
	}	
	
	public void testUVM() throws IOException {
		
//		fDebug = true ;
		
		String test_name = "testBasicExamplePkg" ;
		String bundle_dir_name = "basic_uvm" ;
		String test_bundle_dir = "/data/doc_gen/" + bundle_dir_name ;
		
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
		
		fProject = TestUtils.createProject(testName, projDir) ;
		utils.unpackBundleZipToFS("/uvm.zip", testDir);		
		utils.copyBundleDirToWS(testBundleDir, fProject) ;

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
		
		index.loadIndex(new NullProgressMonitor()) ;
		
		/*
		 * Select all index packages for document generation by
		 * querying the global decl cache for all package decls and
		 * adding them to the DocGenConfig
		 */
		
		DocGenConfig cfg = new DocGenConfig() ;
		
		Map<String,Tuple<SVDBDeclCacheItem, ISVDBIndex>> pkgMap = 
				new HashMap<String, Tuple<SVDBDeclCacheItem,ISVDBIndex>>() ;
	
		List<ISVDBIndex> projIndexList = rgy.getAllProjectLists() ;
		for(ISVDBIndex svdbIndex: projIndexList) {
			List<SVDBDeclCacheItem> foundPkgs = svdbIndex.findGlobalScopeDecl(new NullProgressMonitor(),"pkgs",new SVDBFindPackageMatcher()) ;
			for(SVDBDeclCacheItem pkg: foundPkgs) {
				if(!pkgMap.containsKey(pkg.getName())) { 
					pkgMap.put(
							pkg.getName(), 
							new Tuple<SVDBDeclCacheItem,ISVDBIndex>(pkg,svdbIndex)) ; 
				}
			}
		}		
		
		Set<Tuple<SVDBDeclCacheItem,ISVDBIndex>> pkgs = new HashSet<Tuple<SVDBDeclCacheItem,ISVDBIndex>>(pkgMap.values()) ;
		cfg.setSelectedPackages(pkgs) ;
		
		//
		//
		//
		
		if(fDebug)
			SVCorePlugin.getDefault().enableDebug(true) ;
		
		DocModelFactory factory = new DocModelFactory() ;
		DocModel model = factory.build(cfg) ;
		
		File modelDumpPathAct = new File(testDir, "model_dump_act.txt") ;
		File modelDumpPathExp = new File(cpBundleDir, "model_dump_exp.txt") ;
		
		fLog.debug(ILogLevel.LEVEL_OFF, "+-----------------------------------------------------------") ;
		fLog.debug(ILogLevel.LEVEL_OFF, "| modelDumpPathAct: " + modelDumpPathAct ) ;
		fLog.debug(ILogLevel.LEVEL_OFF, "| modelDumpPathExp: " + modelDumpPathExp ) ;
		fLog.debug(ILogLevel.LEVEL_OFF, "| >>   diff " + modelDumpPathExp + " " + modelDumpPathAct ) ;
		fLog.debug(ILogLevel.LEVEL_OFF, "| >> tkdiff " + modelDumpPathExp + " " + modelDumpPathAct ) ;
		fLog.debug(ILogLevel.LEVEL_OFF, "+-----------------------------------------------------------") ;
		
		FileWriter fw = new FileWriter(modelDumpPathAct.getPath()) ;
		BufferedWriter bw = new BufferedWriter(fw) ;
		model.dumpToFile(bw) ;
		fw.close() ;

		List<String> expLines = TestUtils.fileToLines(modelDumpPathExp.getPath()) ;
		List<String> actLines = TestUtils.fileToLines(modelDumpPathAct.getPath()) ;

		Patch patch = DiffUtils.diff(expLines, actLines) ;

		List<Delta> deltas = patch.getDeltas() ;

		int maxDeltas=20 ;
		int cnt=0 ;
		for(Delta delta: deltas) {
			fLog.error(String.format("Delta %d",cnt)) ;
			fLog.error("Exp: " + delta.getOriginal().toString()) ;
			fLog.error("Act: " + delta.getRevised().toString()) ;
			cnt++ ;
			if(cnt >= maxDeltas) break ;
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
