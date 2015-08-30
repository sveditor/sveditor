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

import java.util.List;

import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.core.scanutils.IBIDITextScanner;
import net.sf.sveditor.core.tests.FileIndexIterator;
import junit.framework.TestCase;
import junit.framework.TestSuite;

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

}
