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


package net.sf.sveditor.core.tests.parser;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.utils.BundleUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestSystemParse extends SVCoreTestCaseBase {
	
	public void testParseOvmSequenceUtils() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		ByteArrayOutputStream bos = utils.readBundleFile("/data/ovm_sequence_utils.svh");
		
		SVDBFile file = SVDBTestUtils.parse(bos.toString(), "ovm_sequence_utils.svh");
		SVDBTestUtils.assertNoErrWarn(file);
	}
	
	public void testRecursiveInclude() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		File tmpdir = fTmpDir;

		PrintStream ps = new PrintStream(new File(tmpdir, "pkg.sv"));
		ps.println("package pkg;");
		ps.println("    `include \"class_1.svh\"");
		ps.println("endpackage");
		ps.close();

		ps = new PrintStream(new File(tmpdir, "class_1.svh"));
		ps.println("`include \"class_1.svh\"");
		ps.println("class class_1;");
		ps.println("endclass");
		ps.close();

		ps = new PrintStream(new File(tmpdir, "pkg.f"));
		ps.println("+incdir+" + tmpdir);
		ps.println("pkg.sv");
		ps.close();

		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(),
				"GLOBAL", new File(tmpdir, "pkg.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE, null);

		index.init(new NullProgressMonitor(), null);

		index.loadIndex(new NullProgressMonitor());

		IndexTestUtils.assertFileHasElements(index, "class_1");
	}
}
