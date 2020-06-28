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
package net.sf.sveditor.core.tests.argfile.creator;

import java.io.File;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.argfile.creator.SVArgFileCreator;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestArgFileCreator extends SVCoreTestCaseBase {
	
	public void testBasicFileDiscovery() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		IProject p = TestUtils.createProject("uvm", new File(fTmpDir, "uvm"));
		addProject(p);
		
		SVArgFileCreator creator = new SVArgFileCreator(new SVDBWSFileSystemProvider());
		
		creator.addSearchPath("${workspace_loc}/uvm/src");
		
		creator.discover_files(new NullProgressMonitor());

		Set<String> paths = creator.getDiscoveredPaths();
	
		for (String path : paths) {
			fLog.debug("path=" + path);
		}
		
		assertTrue(paths.contains("${workspace_loc}/uvm/src/uvm_pkg.sv"));
	}

	public void testRootFileIdentification() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.unpackBundleZipToFS("/wb_dma.zip", fTmpDir);
		
		IProject p = TestUtils.createProject("wb_dma", new File(fTmpDir, "wb_dma"));
		addProject(p);
		
		SVArgFileCreator creator = new SVArgFileCreator(new SVDBWSFileSystemProvider());
		
		creator.addSearchPath("${workspace_loc}/wb_dma");
		
		creator.discover_files(new NullProgressMonitor());

		Set<String> paths = creator.getDiscoveredPaths();
		assertTrue(paths.contains("${workspace_loc}/wb_dma/bench/verilog/tests.v"));
		
		creator.organize_files(new NullProgressMonitor());
		
		List<String> root_files = creator.getRootFiles();
		List<String> incdirs = creator.getIncDirs();
		
		for (String path : root_files) {
			fLog.debug("root_path=" + path);
		}
		
		assertTrue(root_files.contains("${workspace_loc}/wb_dma/rtl/verilog/wb_dma_ch_arb.v"));
		assertFalse(root_files.contains("${workspace_loc}/wb_dma/rtl/verilog/wb_dma_defines.v"));
		
		assertTrue(incdirs.contains("${workspace_loc}/wb_dma/rtl/verilog"));
		assertFalse(incdirs.contains("${workspace_loc}/wb_dma/rtl"));
	}
}
