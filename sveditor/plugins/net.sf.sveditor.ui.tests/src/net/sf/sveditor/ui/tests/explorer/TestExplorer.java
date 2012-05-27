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


package net.sf.sveditor.ui.tests.explorer;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin_lib.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;
import net.sf.sveditor.ui.explorer.PathTreeNode;
import net.sf.sveditor.ui.explorer.PathTreeNodeFactory;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestExplorer extends TestCase {
	private File 						fTmpDir;
	private SVDBIndexCollection		fIndexCollectionOVMMgr;
	
	@Override
	public void setUp() {
		fTmpDir = TestUtils.createTempDir();
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.copyBundleDirToFS("/data/basic_content_assist_project", fTmpDir);

		String pname = "basic_content_assist_project";
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		fIndexCollectionOVMMgr = new SVDBIndexCollection(rgy.getIndexCollectionMgr(), pname);
		fIndexCollectionOVMMgr.addPluginLibrary(
				rgy.findCreateIndex(new NullProgressMonitor(), 
						pname, SVCoreTestsPlugin.OVM_LIBRARY_ID, 
						SVDBPluginLibIndexFactory.TYPE, null));

		// Force database loading
		fIndexCollectionOVMMgr.getItemIterator(new NullProgressMonitor());
	}
	
	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		TestUtils.delete(fTmpDir);
	}
	
	public void testPathTreeNodeFactory() {
		PathTreeNodeFactory f = new PathTreeNodeFactory();
		
		List<ISVDBIndex> l = fIndexCollectionOVMMgr.getPluginPathList();
		
		for (ISVDBIndex i : l) {
			List<SVDBFile> file_l = new ArrayList<SVDBFile>();
			for (String p : i.getFileList(new NullProgressMonitor())) {
				file_l.add(i.findPreProcFile(p));
			}
			List<PathTreeNode> roots = f.build(file_l);
			
			for (PathTreeNode n : roots) {
				System.out.println("root: " + n.getName());
				printChildren("    ", n);
			}
		}
	}
	
	private void printChildren(String indent, PathTreeNode n) {
		System.out.println(indent + "Node: " + n.getName());
		for (SVDBFile f : n.getFileList()) {
			System.out.println(indent + "    File: " + f.getName());
		}
		for (PathTreeNode n_t : n.getChildNodes()) {
			printChildren(indent + "    ", n_t);
		}
	}

}
