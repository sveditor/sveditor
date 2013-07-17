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


package net.sf.sveditor.core.tests.open_decl;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBChildParent;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestStringUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

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
		
		System.out.println("==> parse");
		Tuple<SVDBFile, SVDBFile> parse_r = index.parse(new NullProgressMonitor(), 
				new StringInputStream(in_data),
				uvm_component, null);
		System.out.println("<== parse");
		
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
		
		System.out.println("ret=" + ret + " size=" + ret.size());
		for (Tuple<ISVDBItemBase, SVDBFile> i : ret) {
			ISVDBItemBase item = i.first();
			
			while ((item instanceof ISVDBChildItem) && 
					((ISVDBChildItem)item).getParent() != null &&
					item.getType() != SVDBItemType.File) {
				System.out.println("type=" + item.getType());
				item = ((ISVDBChildItem)item).getParent();
			}
			
			System.out.println("Root: " + item.getType() + " " + ((SVDBFile)item).getFilePath());
			
			SVDBLocation l = i.first().getLocation();
			System.out.println("item: " + i.first() + 
					" file=" + l.getFileId() + " line=" + l.getLine());
		}
	}

}
