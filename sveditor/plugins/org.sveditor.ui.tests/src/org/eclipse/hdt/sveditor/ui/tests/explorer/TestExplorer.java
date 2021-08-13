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


package org.eclipse.hdt.sveditor.ui.tests.explorer;

import java.io.File;

import junit.framework.TestCase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexCollection;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexRegistry;
import org.eclipse.hdt.sveditor.core.db.index.plugin.SVDBPluginLibIndexFactory;

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
