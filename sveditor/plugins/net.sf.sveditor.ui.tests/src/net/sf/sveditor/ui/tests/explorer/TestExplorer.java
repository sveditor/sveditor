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


package net.sf.sveditor.ui.tests.explorer;

import java.io.File;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.plugin.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

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
		fIndexCollectionOVMMgr.loadIndex(new NullProgressMonitor());
	}
	
	@Override
	protected void tearDown() throws Exception {
		super.tearDown();
		
		TestUtils.delete(fTmpDir);
	}
	
}
