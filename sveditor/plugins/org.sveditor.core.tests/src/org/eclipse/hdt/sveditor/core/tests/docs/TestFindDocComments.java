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
package org.eclipse.hdt.sveditor.core.tests.docs;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.tests.FileIndexIterator;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestsPlugin;
import org.eclipse.hdt.sveditor.core.tests.SVDBTestUtils;
import org.eclipse.hdt.sveditor.core.tests.utils.BundleUtils;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBDocComment;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindDocComment;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindNamedClass;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class TestFindDocComments extends SVCoreTestCaseBase {
	
	public void testFindUvmReportObject() {
		String testname = "testFindUvmReportObject";
		LogHandle log = LogFactory.getLogHandle(testname);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		SVCorePlugin.getDefault().enableDebug(false);
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		File uvm = new File(fTmpDir, "uvm");

		File uvm_report_object_svh = new File(uvm, "src/base/uvm_report_object.svh");
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		
		Tuple<SVDBFile, SVDBFile> file = SVDBTestUtils.parse(log, uvm_report_object_svh, markers); 
	
		assertNotNull(file);

		ISVDBIndexCache cache = FileIndexIterator.createCache(fCacheFactory);
		FileIndexIterator index_it = new FileIndexIterator(file, cache);
		
		SVDBFindNamedClass finder = new SVDBFindNamedClass(index_it);
		List<SVDBClassDecl> result = finder.findItem("uvm_report_object");
		
		assertTrue(result.size() == 1);
		
		SVDBClassDecl uvm_report_object = result.get(0);
		
		SVDBFindDocComment comment_finder = new SVDBFindDocComment(index_it);
		
		SVDBDocComment comment = comment_finder.find(new NullProgressMonitor(), uvm_report_object);
		
		assertNotNull(comment);
	}

}
