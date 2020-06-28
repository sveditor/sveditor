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

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexInt;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.plugin.SVDBPluginLibIndexFactory;
import net.sf.sveditor.core.preproc.ISVPreProcessor;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

public class TestVmmBasics extends SVCoreTestCaseBase {

	// Doing something wrong? Examples work
	public void disabled_testBasicProcessing() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		rgy.init(fCacheFactory);
	
		SVDBIndexCollection index_mgr = new SVDBIndexCollection("GLOBAL");
		index_mgr.addPluginLibrary(
				rgy.findCreateIndex(new NullProgressMonitor(), "GLOBAL", "org.vmmcentral.vmm", 
						SVDBPluginLibIndexFactory.TYPE, null));
		index_mgr.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index_mgr);
		IndexTestUtils.assertFileHasElements(fLog, index_mgr, 
				"vmm_xtor");
	}
	
	public void testEthernetExample() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);
		
		File test_dir = new File(fTmpDir, "testEthernetExample");
		assertTrue(test_dir.mkdirs());
	
		utils.unpackBundleZipToFS("/vmm.zip", test_dir);
		File ethernet = new File(test_dir, "vmm/sv/examples/std_lib/ethernet");
		
		IProject project = TestUtils.createProject("ethernet", ethernet);
		addProject(project);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(),
				"GENERIC", "${workspace_loc}/ethernet/ethernet.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.init(new NullProgressMonitor(), null);
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
	}

	public void testWishboneExample() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testWishboneExample");
		if (test_dir.exists()) {
			TestUtils.delete(test_dir);
		}
		test_dir.mkdirs();
		
		utils.unpackBundleZipToFS("/vmm.zip", test_dir);
		File wishbone = new File(test_dir, "vmm/sv/examples/std_lib/wishbone");
		
		IProject project = TestUtils.createProject("wishbone", wishbone);
		addProject(project);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), 
				"GENERIC", "${workspace_loc}/wishbone/wishbone.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.loadIndex(new NullProgressMonitor());
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
	}

	public void disabled_testScenariosExample() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		File test_dir = new File(fTmpDir, "testScenariosExample");
		assertTrue(test_dir.mkdirs());
		
		utils.unpackBundleZipToFS("/vmm.zip", test_dir);
		File scenarios = new File(test_dir, "vmm/sv/examples/std_lib/scenarios");

		IProject project = TestUtils.createProject("scenarios", scenarios);
		addProject(project);
		
		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/scenarios/scenarios.f",
				SVDBArgFileIndexFactory.TYPE, null);
		index.execIndexChangePlan(new NullProgressMonitor(), new SVDBIndexChangePlanRebuild(index));
		
		final ISVDBIndexInt af_index = (ISVDBIndexInt)index;
		// ISVDBFileSystemProvider fs_p = af_index.getFileSystemProvider();
		final Tuple<ISVPreProcessor, ISVPreProcessor> result = new Tuple<ISVPreProcessor, ISVPreProcessor>(null, null);
		
		ISVDBIndexOperation op = new ISVDBIndexOperation() {
			
			public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
				ISVPreProcessor pp = af_index.createPreProcScanner("${workspace_loc}/scenarios/simple_sequencer.sv");
				result.setFirst(pp);
			}
		};
		af_index.execOp(new NullProgressMonitor(), op, true);
		
		ISVPreProcessor pp = result.first();
		assertNotNull(pp);
	
		SVPreProcOutput pp_out = pp.preprocess();
		
		int ch, lineno=1;
		StringBuilder sb_dbg = new StringBuilder();
		sb_dbg.append(lineno + ": ");
		StringBuilder sb = new StringBuilder();
		while ((ch = pp_out.get_ch()) != -1) {
			sb_dbg.append((char)ch);
			sb.append((char)ch);
			if (ch == '\n') {
				lineno++;
				sb_dbg.append(lineno + ": ");
			}
		}
		fLog.debug("Content\n" + sb_dbg.toString());
		
		SVDBTestUtils.parse(fLog, sb.toString(), "preProcessed.simple_sequencer.sv", false);
		
		
		IndexTestUtils.assertNoErrWarn(fLog, index);
	}
}
