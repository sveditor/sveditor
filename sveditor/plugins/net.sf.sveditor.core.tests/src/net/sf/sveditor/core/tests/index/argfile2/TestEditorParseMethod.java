package net.sf.sveditor.core.tests.index.argfile2;


import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.BundleUtils;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.parser.ParserTests;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestEditorParseMethod extends SVCoreTestCaseBase {
	
	public void testSFCUIncomingMacros() {
		SVCorePlugin.getDefault().enableDebug(true);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		utils.copyBundleDirToFS("/data/index/sfcu_cross_file_macros", fTmpDir);
		
		File sfcu_cross_file_macros = new File(fTmpDir, "sfcu_cross_file_macros");
		TestUtils.createProject("sfcu_cross_file_macros", sfcu_cross_file_macros);

		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(),
				"sfcu_cross_file_macros",
				"${workspace_loc}/sfcu_cross_file_macros/sfcu_cross_file_macros.f",
				SVDBArgFileIndexFactory.TYPE, null);
	
		IndexTestUtils.assertNoErrWarn(fLog, index);
		
		IndexTestUtils.assertFileHasElements(fLog, index, 
				"pkg1_cls1",
				"pkg1_cls2");
		
		List<SVDBMarker> markers;
		Tuple<SVDBFile, SVDBFile> result;

		// First, test that macros propagate from package down to included files
		markers = new ArrayList<SVDBMarker>();
		result = IndexTestUtils.parse(index, 
				"${workspace_loc}/sfcu_cross_file_macros/pkg1_cls1.svh", markers);
		assertEquals(0, markers.size());
		
		SVDBTestUtils.assertFileHasElements(result.second(),
				"pkg1_cls1");
		
		// Next, test that macros propagate across included files
		markers = new ArrayList<SVDBMarker>();
		result = IndexTestUtils.parse(index, 
				"${workspace_loc}/sfcu_cross_file_macros/pkg2_cls2.svh", markers);
		assertEquals(0, markers.size());
		
		SVDBTestUtils.assertFileHasElements(result.second(),
				"pkg2_cls2");
	}

	public void testMFCUIncomingMacros() {
		SVCorePlugin.getDefault().enableDebug(true);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		utils.copyBundleDirToFS("/data/index/mfcu_cross_file_macros", fTmpDir);
		
		File mfcu_cross_file_macros = new File(fTmpDir, "mfcu_cross_file_macros");
		TestUtils.createProject("mfcu_cross_file_macros", mfcu_cross_file_macros);

		ISVDBIndex index = fIndexRgy.findCreateIndex(
				new NullProgressMonitor(),
				"mfcu_cross_file_macros",
				"${workspace_loc}/mfcu_cross_file_macros/mfcu_cross_file_macros.f",
				SVDBArgFileIndexFactory.TYPE, null);
	
		IndexTestUtils.assertNoErrWarn(fLog, index);
		
		IndexTestUtils.assertFileHasElements(fLog, index, 
				"pkg1_cls1",
				"pkg1_cls2");
		
		List<SVDBMarker> markers;
		Tuple<SVDBFile, SVDBFile> result;

		// First, test that macros propagate from package down to included files
		markers = new ArrayList<SVDBMarker>();
		result = IndexTestUtils.parse(index, 
				"${workspace_loc}/mfcu_cross_file_macros/pkg1_cls1.svh", markers);
		assertEquals(0, markers.size());
		
		SVDBTestUtils.assertFileHasElements(result.second(),
				"pkg1_cls1");
		
		// Next, test that macros propagate across included files
		markers = new ArrayList<SVDBMarker>();
		result = IndexTestUtils.parse(index, 
				"${workspace_loc}/mfcu_cross_file_macros/pkg2_cls2.svh", markers);
		assertEquals(0, markers.size());
		
		SVDBTestUtils.assertFileHasElements(result.second(),
				"pkg2_cls2");
	}
}


