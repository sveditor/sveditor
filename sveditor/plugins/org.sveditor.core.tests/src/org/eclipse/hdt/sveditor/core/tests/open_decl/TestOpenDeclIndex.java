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


package org.eclipse.hdt.sveditor.core.tests.open_decl;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.List;

import org.eclipse.hdt.sveditor.core.tests.IndexTestUtils;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.TestStringUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildItem;
import org.eclipse.hdt.sveditor.core.db.ISVDBChildParent;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import org.eclipse.hdt.sveditor.core.open_decl.OpenDeclUtils;
import org.eclipse.hdt.sveditor.core.scanutils.StringBIDITextScanner;

public class TestOpenDeclIndex extends SVCoreTestCaseBase {

	public void testUVMOpenDecl() throws IOException, CoreException {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		File uvm = new File(fTmpDir, "uvm");
	
		IProject project = TestUtils.createProject("uvm", uvm);
		addProject(project);
	
		String uvm_component = "${workspace_loc}/uvm/src/base/uvm_component.svh";
		IFile uvm_f = project.getFile("src/uvm.f");
		String uvm_f_s = 
		  "+incdir+.\n" +
		  "+define+QUESTA\n" +
		  "uvm_pkg.sv\n";
		
		uvm_f.create(new StringInputStream(uvm_f_s),
				true, new NullProgressMonitor());
				
		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), "GENERIC",
				"${workspace_loc}/uvm/src/uvm.f",
				SVDBArgFileIndexFactory.TYPE,
				null);
		
		index.loadIndex(new NullProgressMonitor());

		IndexTestUtils.assertNoErrWarn(fLog, index);

		InputStream in = index.getFileSystemProvider().openStream(uvm_component);
		assertNotNull(in);
		String in_data = SVFileUtils.readInput(in);
		index.getFileSystemProvider().closeStream(in);
		
		fLog.debug("==> parse");
		Tuple<SVDBFile, SVDBFile> parse_r = index.parse(new NullProgressMonitor(), 
				new StringInputStream(in_data),
				uvm_component, null);
		fLog.debug("<== parse");
		
		assertNotNull(parse_r);
//		assertNotNull(parse_r.first());
		assertNotNull(parse_r.second());
		
//		SVCorePlugin.getDefault().enableDebug(false);
		StringBIDITextScanner scanner = new StringBIDITextScanner(in_data);
		
		int idx = in_data.indexOf("uvm_component extends uvm_report_object");
		assertTrue((idx > 0));

		idx += "uvm_component extends uvm".length();
		scanner.seek(idx);
		
		int line = TestStringUtils.lineOfIndex(in_data, idx);
		
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				parse_r.second(), line, scanner, index);
		
		fLog.debug("ret=" + ret + " size=" + ret.size());
		assertEquals("Failed to find uvm_component declaration", 1, ret.size());
		ISVDBItemBase item = ret.get(0).first();

		while ((item instanceof ISVDBChildItem) && 
				((ISVDBChildItem)item).getParent() != null &&
				item.getType() != SVDBItemType.File) {
			fLog.debug("type=" + item.getType());
			item = ((ISVDBChildItem)item).getParent();
		}

		String path = ((SVDBFile)item).getFilePath();

		fLog.debug("path=" + path);
		assertTrue(path.endsWith("uvm_report_object.svh"));

	}

}
