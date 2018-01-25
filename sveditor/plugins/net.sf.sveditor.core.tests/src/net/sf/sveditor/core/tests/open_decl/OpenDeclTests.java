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


package net.sf.sveditor.core.tests.open_decl;

import java.io.File;
import java.util.List;

import org.eclipse.core.runtime.NullProgressMonitor;

import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuild;
import net.sf.sveditor.core.db.index.builder.SVDBIndexChangePlanRebuildFiles;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.core.preproc.ISVPreProcessor;
import net.sf.sveditor.core.preproc.ISVStringPreProcessor;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class OpenDeclTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("OpenDeclTests");
//		s.addTest(new TestSuite(TestOpenFile.class));
		s.addTest(new TestSuite(TestOpenClass.class));
		s.addTest(new TestSuite(TestOpenMethod.class));
		s.addTest(new TestSuite(TestOpenModIfc.class));
		s.addTest(new TestSuite(TestOpenDeclIndex.class));
		s.addTest(new TestSuite(TestOpenDeclUBus.class));
		
		return s;
	}

	public static List<Tuple<ISVDBItemBase, SVDBFile>> runOpenDeclOp(
			ISVDBIndexCacheMgr	cache_factory,
			SVDBFile			file,
			int					lineno,
			IBIDITextScanner	scanner
			) {
		ISVDBIndexCache cache = FileIndexIterator.createCache(cache_factory);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);		
		return OpenDeclUtils.openDecl_2(
				file, lineno, scanner, target_index);
	}
	
	public static void validatePathToFile(ISVDBItemBase it) {
		TestCase.assertTrue((it instanceof ISVDBChildItem));
		
		ISVDBChildItem ci = (ISVDBChildItem)it;
		
		while (ci != null && ci.getType() != SVDBItemType.File) {
			ci = ci.getParent();
		}
		
		TestCase.assertNotNull(ci);
	}
	
	public static void runTest(
			SVCoreTestCaseBase		test,
			String					doc,
			int						offset,
			String					name,
			SVDBItemType			type) {
		LogHandle log = test.getLog();
		File tmpdir = test.getTmpDir();
		int idx = doc.indexOf("<<MARK>>");
		TestCase.assertNotSame(-1, idx);
		
		String clean_doc = doc.replace("<<MARK>>", "");
	
		StringBIDITextScanner scanner = new StringBIDITextScanner(clean_doc);
		log.debug("index: " + idx);
		scanner.seek(idx+offset);
		
		TestUtils.copy(
				clean_doc,
				new File(tmpdir, test.getName() + ".sv"));
		TestUtils.copy(
				new File(tmpdir, test.getName() + ".sv").getAbsolutePath(),
				new File(tmpdir, test.getName() + ".f"));
		
		ISVDBIndex index = test.getIndexRgy().findCreateIndex(
				new NullProgressMonitor(),
				"test",
				new File(tmpdir, test.getName() + ".f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE,
				null);
		
		index.execIndexChangePlan(new NullProgressMonitor(), 
				new SVDBIndexChangePlanRebuild(index));
	
		String test_sv = SVFileUtils.normalize(
				new File(tmpdir, test.getName() + ".sv").getAbsolutePath());
		SVDBFile file = index.findFile(test_sv);
		
		TestCase.assertNotNull(file);
		
		int lineno = 1;
		for (int i=0; i<(idx+offset); i++) {
			if (clean_doc.charAt(i) == '\n') {
				lineno++;
			}
		}
		
		ISVStringPreProcessor p = index.createPreProc(
				test_sv, 
				new StringInputStream(clean_doc), 
				-1);
		
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file, lineno, scanner, p, index);
		
		TestCase.assertEquals(1,  ret.size());
		TestCase.assertEquals(type, ret.get(0).first().getType());
		TestCase.assertEquals(name,  SVDBItem.getName(ret.get(0).first()));
	}

}
