/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.tests.index.argfile2;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexChangeListener;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexChangeEvent;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexCollection;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectData;
import org.eclipse.hdt.sveditor.core.db.project.SVDBProjectManager;
import org.eclipse.hdt.sveditor.core.db.project.SVProjectFileWrapper;
import org.eclipse.hdt.sveditor.core.job_mgr.IJobMgr;

import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.index.IndexTests;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestArgFileChange extends SVCoreTestCaseBase {
	private List<Integer>		fEvents = new ArrayList<Integer>();
	private List<Integer>		fIndexChangeEvents = new ArrayList<Integer>();
	private List<ISVDBIndex>	fRegisteredIndexes = new ArrayList<ISVDBIndex>();
	private Object				fSharedEvent = new Object();
	
	IResourceChangeListener 	fListener = new IResourceChangeListener() {
		
		@Override
		public void resourceChanged(IResourceChangeEvent event) {
			synchronized (fEvents) {
				fEvents.add(1);
				fEvents.notifyAll();
			}
			synchronized (fSharedEvent) {
				fSharedEvent.notifyAll();
			}
		}
	};
	
	ISVDBIndexChangeListener 	fIndexChangeListener = new ISVDBIndexChangeListener() {
		@Override
		public void index_event(SVDBIndexChangeEvent e) {
			fLog.debug("index_event: " + e.getType() + " index: " + e.getIndex());
			synchronized (fIndexChangeEvents) {
				fIndexChangeEvents.add(1);
				fIndexChangeEvents.notifyAll();
			}
			synchronized (fSharedEvent) {
				fSharedEvent.notifyAll();
			}			
		}
	};
	
	@Override
	protected void setUp() throws Exception {
		super.setUp();
		ResourcesPlugin.getWorkspace().addResourceChangeListener(fListener);
	}

	@Override
	protected void tearDown() throws Exception {
		waitIndexEvent(100); // Just wait for a bit
		
		super.tearDown();
		ResourcesPlugin.getWorkspace().removeResourceChangeListener(fListener);
		
		for (ISVDBIndex i : fRegisteredIndexes) {
			i.removeChangeListener(fIndexChangeListener);
		}
		fRegisteredIndexes.clear();
	}
	
	private void addIndex(ISVDBIndex i) {
		fRegisteredIndexes.add(i);
		i.addChangeListener(fIndexChangeListener);
	}
	
	private void addIndex(SVDBIndexCollection i) {
		for (ISVDBIndex ii : i.getIndexList()) {
			addIndex(ii);
		}
	}
	
	private void clearEvents() {
		synchronized (fEvents) {
			fEvents.clear();
		}
	}
	
	private boolean waitEvent() {
		return waitEvent(10000);
	}
	
	private boolean waitEvent(int timeout) {
		boolean ret = false;
		
		synchronized (fEvents) {
			ret = (fEvents.size() > 0);
			fEvents.clear();
		}
		
		if (!ret) {
			try {
				synchronized (fEvents) {
					fEvents.wait(timeout);
					ret = (fEvents.size() > 0);
					fEvents.clear();
				}
			} catch (InterruptedException e) { }
		}

		return ret;
	}

	private boolean waitIndexEvent(int timeout) {
		boolean ret = false;
		
		synchronized (fIndexChangeEvents) {
			ret = (fIndexChangeEvents.size() > 0);
			fIndexChangeEvents.clear();
		}
		
		if (ret) {
			fLog.debug("Note: early exit from waitIndexEvent");
			synchronized (fEvents){
				fEvents.clear();
			}
			return ret;
		}
		
		synchronized (fIndexChangeEvents) {
			try {
				fIndexChangeEvents.wait(timeout);
			} catch (InterruptedException e) {
				System.out.println("Interrupted");
			}
			ret = (fIndexChangeEvents.size() > 0);
			fIndexChangeEvents.clear();
		}
		synchronized (fEvents){
			fEvents.clear();
		}
		
		fLog.debug("Note: normal exit from waitIndexEvent: " + ret);
	
		return ret;
	}
	
	private boolean waitIndexEvent() {
		return waitIndexEvent(20000);
	}

	public void testRootFileAdd_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
	}

	public void testRootFileChangeSrcFile_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
	
		// Rewrite the root file so it contains my_pkg2 rather than my_pkg
		SVFileUtils.copy(
				"package my_pkg2;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		
		assertTrue(waitIndexEvent());
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg2", SVDBItemType.PackageDecl);
		IndexTests.assertDoesNotContain(pd.getProjectIndexMgr(), "my_pkg");
	}

	public void testRootFileRemoveSrcFile_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv")));
		
		SVFileUtils.copy(
				"package my_pkg2;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg2.sv")));
		
		SVFileUtils.copy(
				"./my_pkg.sv\n" + 
				"./my_pkg2.sv\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg2", SVDBItemType.PackageDecl);
	
		// Rewrite the sve.f so it doesn't contain my_pkg2
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));

		assertTrue(waitIndexEvent());
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertDoesNotContain(pd.getProjectIndexMgr(), "my_pkg2");
	}

	public void testRootFileRemoveSrcFileLeaveRef_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv")));
		
		SVFileUtils.copy(
				"package my_pkg2;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg2.sv")));
		
		SVFileUtils.copy(
				"./my_pkg.sv\n" + 
				"./my_pkg2.sv\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg2", SVDBItemType.PackageDecl);

		// Delete my_pkg2.sv
		SVFileUtils.delete(p.getFile(new Path("my_pkg2.sv")));
	
		assertTrue(waitIndexEvent());
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertDoesNotContain(pd.getProjectIndexMgr(), "my_pkg2");
	}

	public void testRootFileRemoveFileListLeaveRef_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		fLog.debug("--> Wait for rebuild event (1)");
		addIndex(pd.getProjectIndexMgr());
		fLog.debug("<-- Wait for rebuild event (1)");

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv")));
		
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("my_pkg.f")));
		
		SVFileUtils.copy(
				"package my_pkg2;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg2.sv")));
		
		SVFileUtils.copy(
				"./my_pkg2.sv\n",
				p.getFile(new Path("my_pkg2.f")));
		
		SVFileUtils.copy(
				"-f ./my_pkg.f\n" + 
				"-f ./my_pkg2.f\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event (2)");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event (2)");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg2", SVDBItemType.PackageDecl);

		// Delete my_pkg2.sv
		SVFileUtils.delete(p.getFile(new Path("my_pkg2.f")));
	
		fLog.debug("--> Wait for rebuild event (3)");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event (3)");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertDoesNotContain(pd.getProjectIndexMgr(), "my_pkg2");
	}
	
	public void testRootFileChangeIncSrcFile_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");
		
		SVFileUtils.copy(
				"\n",
				p.getFile(new Path("my_cls.svh"))
				);

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"`include \"my_cls.svh\"\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
		IndexTests.assertDoesNotContain(
				pd.getProjectIndexMgr(), "my_cls");
	
		// Rewrite the included file so it does declare a class
		SVFileUtils.copy(
				"class my_cls;\n" +
				"endclass\n",
				p.getFile(new Path("my_cls.svh"))
				);
		
		assertTrue(waitIndexEvent());
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_cls", SVDBItemType.ClassDecl);
	}
	
	public void testRootFileChangeFileList_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		IProject p = TestUtils.createProject(getName(), 
				new File(fTmpDir, getName()));
		addProject(p);
	
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		SVDBProjectData pd = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pd.getProjectFileWrapper();
		
		SVFileUtils.copy(
				"// Empty file\n",
				p.getFile(new Path("sve.f")));
		
		fw.addArgFilePath("${project_loc}/sve.f");
		pd.setProjectFileWrapper(fw);
		
		addIndex(pd.getProjectIndexMgr());

		// Sleep for 1ms
		fLog.debug("--> Wait for initial event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for initial event");

		SVFileUtils.copy(
				"package my_pkg;\n" +
				"endpackage\n",
				p.getFile(new Path("my_pkg.sv"))
				);
		
		SVFileUtils.copy(
				"./my_pkg.sv\n",
				p.getFile(new Path("my_pkg.f")));
		
		SVFileUtils.copy(
				"-f ./my_pkg.f\n",
				p.getFile(new Path("sve.f")));
		
		fLog.debug("--> Wait for rebuild event");
		assertTrue(waitIndexEvent());
		fLog.debug("<-- Wait for rebuild event");
		
		IndexTests.assertContains(pd.getProjectIndexMgr(), 
				"my_pkg", SVDBItemType.PackageDecl);
	}	
}
