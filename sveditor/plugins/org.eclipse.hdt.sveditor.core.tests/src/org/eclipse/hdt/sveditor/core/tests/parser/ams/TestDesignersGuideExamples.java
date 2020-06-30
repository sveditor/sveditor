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
package net.sf.sveditor.core.tests.parser.ams;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.parser.SVLanguageLevel;

import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;

public class TestDesignersGuideExamples extends SVCoreTestCaseBase {
	
	public void testCh3Listing02() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing02.tar");
	}
	
	public void testCh3Listing03() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing03.tar");
	}
	
	public void testCh3Listing04() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing04.tar");
	}
	
	public void testCh3Listing05() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing05.tar");
	}
	
	public void testCh3Listing06() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing06.tar");
	}
	
	public void testCh3Listing13() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing13.tar");
	}
	
	public void testCh3Listing14() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing14.tar");
	}
	
	public void testCh3Listing15() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing15.tar");
	}

	public void testCh3Listing16() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing16.tar");
	}
	
	public void testCh3Listing17() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing17.tar");
	}
	
	public void testCh3Listing18() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing18.tar");
	}
	
	public void testCh3Listing19() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing19.tar");
	}
	
	// TODO: 20
	
	public void testCh3Listing21() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing21.tar");
	}
	
	public void testCh3Listing22() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing22.tar");
	}
	
	public void testCh3Listing23() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing23.tar");
	}
	
	public void testCh3Listing24() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing24.tar");
	}
	
	public void testCh3Listing25() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing25.tar");
	}
	
	public void testCh3Listing26() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing26.tar");
	}
	
	public void testCh3Listing27() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch3-listing27.tar");
	}

	/*
	public void testCh4Listing01() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch4-listing01.tar");
	}
	 */
	
	public void testCh4Listing03() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch4-listing03.tar");
	}
	
	/*
	public void testCh4Listing04() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch4-listing04.tar");
	}
	
	public void testCh4Listing05() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch4-listing05.tar");
	}
	
	public void testCh4Listing06() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch4-listing06.tar");
	}
	
	public void testCh4Listing07() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch4-listing07.tar");
	}
	
	public void testCh4Listing08() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch4-listing08.tar");
	}
	 */
	
	public void testCh5Listing01() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		testExample("/data/ams/ch4-listing01.tar");
	}
	
	private void testExample(String path) throws IOException {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());

		if (path.endsWith(".tar.gz") || path.endsWith(".tgz")) {
			utils.unpackBundleTgzToFS(path, fTmpDir);
		} else if (path.endsWith(".tar")) {
			utils.unpackBundleTarToFS(path, fTmpDir);
		}
		
		String dirname = (new File(path)).getName();
		dirname = dirname.substring(dirname.indexOf('-')+1);
		dirname = dirname.substring(0, dirname.indexOf('.'));
		
		File testdir = new File(fTmpDir, dirname);
		
		assertTrue(testdir.isDirectory());
	
		File ams_file = null;
		
		for (File f : testdir.listFiles()) {
			if (f.getName().endsWith(".vams") || 
					f.getName().equals("testbench.v")) {
				assertNull("multiple AMS files", ams_file);
				ams_file = f;
			}
		}
		
		
		assertNotNull("Failed to find AMS file", ams_file);
		
		InputStream in = new FileInputStream(ams_file);
	
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		SVDBTestUtils.parse(fLog, SVLanguageLevel.VerilogAMS, null,
				in, ams_file.getName(), markers);
	
		if (markers.size() > 0) {
			fLog.debug("Errors for " + path);
			for (SVDBMarker m : markers) {
				fLog.debug("  ERROR: " + m.getMessage() + ":" + 
						SVDBLocation.unpackLineno(m.getLocation()));
			}
		}
	
		assertEquals(0,  markers.size());
	}

}
