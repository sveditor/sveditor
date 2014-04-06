/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Armond Paiva - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.objects;

import java.util.List;

import junit.framework.Test;
import junit.framework.TestSuite;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.objects.ObjectsTreeFactory;
import net.sf.sveditor.core.objects.ObjectsTreeNode;
import net.sf.sveditor.core.tests.CoreReleaseTests;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

public class ObjectsTests extends SVCoreTestCaseBase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("Objects");
		suite.addTest(new TestSuite(ObjectsTests.class));
		return suite;
	}

	private SVDBProjectData 		fp1_pdata, fp2_pdata ;
	private SVProjectFileWrapper 	fp1_fwrapper, fp2_fwrapper ;
	private ObjectsTreeNode 		fTopNode ;
	private	ObjectsTreeNode 		fpkgsNode=null, fmodulesNode=null, finterfacesNode=null ;
	private	ObjectsTreeNode 		fpkgA=null, fpkgB=null, fpkgRoot=null ;
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		
		SVCorePlugin.getDefault().enableDebug(false);
		CoreReleaseTests.clearErrors();
		
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
//		rgy.init(fCacheFactory);
		
		// Projec p1
		
		IProject fp1 = TestUtils.setupIndexWSProject(
				null, fTmpDir, "p1", 
				"/data/objects/p1");
		addProject(fp1);
		
		IProject fp2 = TestUtils.setupIndexWSProject(
				null, fTmpDir, "p2", 
				"/data/objects/p2");
		addProject(fp2);
		
		fp1_pdata = pmgr.getProjectData(fp1);
		fp1_fwrapper = fp1_pdata.getProjectFileWrapper();
		fp1_fwrapper.addArgFilePath("${workspace_loc}/p1/p1/p1.f");

		fp1_pdata.setProjectFileWrapper(fp1_fwrapper);
	
		SVDBIndexCollection p1_index = fp1_pdata.getProjectIndexMgr();
		for (ISVDBIndex index : p1_index.getIndexList()) {
			index.loadIndex(new NullProgressMonitor());
		}
		
		// Projec p2
		
		fp2_pdata = pmgr.getProjectData(fp2);
		fp2_fwrapper = fp2_pdata.getProjectFileWrapper();
		fp2_fwrapper.addArgFilePath("${workspace_loc}/p2/p2/p2.f");

		fp2_pdata.setProjectFileWrapper(fp2_fwrapper);
	
		SVDBIndexCollection p2_index = fp2_pdata.getProjectIndexMgr();
		for (ISVDBIndex index : p2_index.getIndexList()) {
			index.loadIndex(new NullProgressMonitor());
		}
		
		//
		
		List<ISVDBIndex> allProjIndexList = p1_index.getIndexList() ;
		
		allProjIndexList.addAll(p2_index.getIndexList()) ;
		
		ObjectsTreeFactory of = new ObjectsTreeFactory(allProjIndexList) ;
		
		//
		
		fTopNode = of.build() ;
		
		if(fTopNode != null) {
			for(ObjectsTreeNode topChild: fTopNode.getChildren()) {
				if(topChild.getName() == ObjectsTreeNode.PACKAGES_NODE) {
					fpkgsNode = topChild ;
					continue ;
				}
				if(topChild.getName() == ObjectsTreeNode.MODULES_NODE) {
					fmodulesNode = topChild ;
					continue ;
				}
				if(topChild.getName() == ObjectsTreeNode.INTERFACES_NODE) {
					finterfacesNode = topChild ;
					continue ;
				}
			}
		}
		
		if(fpkgsNode != null) {
			for(ObjectsTreeNode pkgNode: fpkgsNode.getChildren()) {
				if(pkgNode.getName().matches("pkgA")){
					fpkgA = pkgNode ;
					continue ;
				}
				if(pkgNode.getName().matches("pkgB")){
					fpkgB = pkgNode ;
					continue ;
				}
				if(pkgNode.getName().matches(ObjectsTreeNode.ROOT_PKG)) {
					fpkgRoot = pkgNode ;
					continue ;
				}
			}
		}
		
	    	
	}

	@Override
	protected void tearDown() throws Exception {
		SVCorePlugin.getDefault().getSVDBIndexRegistry().close();
		SVCorePlugin.getJobMgr().dispose();
		
		assertEquals(0, CoreReleaseTests.getErrors().size());
		
		super.tearDown();
	}

	public void testTopNodeFound() throws CoreException {
		assertNotNull(fTopNode) ;
	}
	
	public void testTopNodesFound() throws CoreException {
		
		assertNotNull("Packages top node not created by factory", fpkgsNode) ;
		assertNotNull("Modules top node not created by factory", fmodulesNode) ;
		assertNotNull("Interfaces top node not created by factory", finterfacesNode) ;
		
	}
	
	public void testPackagesFound() throws CoreException {
		
		assertNotNull("pkg A not found", fpkgA) ;
		assertNotNull("pkg B not found", fpkgB) ;
		assertNotNull("pkg Root not found", fpkgRoot) ;
		
	}
	
	public void testClassesNotWithinPackages() throws CoreException {
		
		assertNotNull("pkg Root not found", fpkgRoot) ;
		
		ObjectsTreeNode cR=null, cS=null ;
		
		if(fpkgRoot != null) {
			cR = fpkgRoot.getChildByName("cR") ;
			cS = fpkgRoot.getChildByName("cS") ;
		}
		
		assertNotNull("class cR not found in root package", cR) ;
		assertNotNull("class cS not found in root package", cS) ;
	}
	
	public void testClassesWithinPackages() throws CoreException {  
		SVCorePlugin.getDefault().enableDebug(false);
		
		assertNotNull("pkg A not found", fpkgA) ;
		assertNotNull("pkg B not found", fpkgB) ;
		assertNotNull("pkg C not found", fpkgB) ;
		
		ObjectsTreeNode cA=null, cB=null, cL=null ;
		
		cA = fpkgA.getChildByName("cA") ;
		cB = fpkgA.getChildByName("cB") ;
		
		cL = fpkgB.getChildByName("cL") ;
		
		assertNotNull("class cA not found in pkgA", cA) ;
		assertNotNull("class cB not found in pkgA", cB) ;
		assertNotNull("class cL not found in pkgB", cL) ;
	
	}

}
