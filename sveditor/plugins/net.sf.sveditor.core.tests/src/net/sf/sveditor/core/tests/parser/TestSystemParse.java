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


package net.sf.sveditor.core.tests.parser;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.db.index.SVDBLibPathIndexFactory;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import net.sf.sveditor.core.tests.TestNullIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestSystemParse extends TestCase {
	
	public void testParseOvmSequenceUtils() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		ByteArrayOutputStream bos = utils.readBundleFile("/data/ovm_sequence_utils.svh");
		
		SVDBFile file = SVDBTestUtils.parse(bos.toString(), "ovm_sequence_utils.svh");
		SVDBTestUtils.assertNoErrWarn(file);
	}
	
	public void testRecursiveInclude() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		File tmpdir = TestUtils.createTempDir();
		
		try {
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
			
			SVDBIndexRegistry rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
			rgy.init(new TestNullIndexCacheFactory());
			SVDBFSFileSystemProvider fs = new SVDBFSFileSystemProvider();
			fs.init(tmpdir.getAbsolutePath());
			ISVDBIndex index = rgy.findCreateIndex(new NullProgressMonitor(),
					"GLOBAL", new File(tmpdir, "pkg.sv").getAbsolutePath(),
					SVDBLibPathIndexFactory.TYPE, null);
			
			index.loadIndex(new NullProgressMonitor());
			ISVDBItemIterator it = index.getItemIterator(new NullProgressMonitor());
			ISVDBItemBase class_1 = null;
			
			while (it.hasNext()) {
				ISVDBItemBase i = it.nextItem();
				if (SVDBItem.getName(i).equals("class_1")) {
					class_1 = i;
				}
			}
			
			assertNotNull(class_1);
			
		} finally {
			TestUtils.delete(tmpdir);
		}
	}
}
