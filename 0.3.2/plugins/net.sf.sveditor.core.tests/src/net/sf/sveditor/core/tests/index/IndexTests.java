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


package net.sf.sveditor.core.tests.index;

import java.util.ArrayList;
import java.util.List;

import junit.framework.Test;
import junit.framework.TestSuite;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.tests.index.libIndex.WSArgFileIndexChanges;
import net.sf.sveditor.core.tests.index.libIndex.WSLibIndexFileChanges;
import net.sf.sveditor.core.tests.index.src_collection.SrcCollectionBasics;

public class IndexTests extends TestSuite {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("IndexTests");
		suite.addTest(new TestSuite(WSLibIndexFileChanges.class));
		suite.addTest(new TestSuite(WSArgFileIndexChanges.class));
		suite.addTest(new TestSuite(SrcCollectionBasics.class));
		suite.addTest(new TestSuite(TestBuiltinIndex.class));
		suite.addTest(new TestSuite(SrcCollectionBasics.class));
		suite.addTest(new TestSuite(TestIndexMissingIncludeDefine.class));
		suite.addTest(new TestSuite(TestGlobalDefine.class));
		suite.addTest(new TestSuite(TestVmmBasics.class));
		suite.addTest(new TestSuite(TestOvmBasics.class));
		suite.addTest(new TestSuite(TestIndexParse.class));
		suite.addTest(new TestSuite(TestArgFileIndex.class));
		suite.addTest(new TestSuite(TestIndexPersistance.class));
		
		return suite;
	}
	
	public static List<SVDBMarkerItem> getErrorsWarnings(ISVDBIndexIterator index_it) {
		ISVDBItemIterator<SVDBItem> it = index_it.getItemIterator();
		List<SVDBMarkerItem> ret = new ArrayList<SVDBMarkerItem>();
		
		while (it.hasNext()) {
			SVDBItem it_t = it.nextItem();
			if (it_t.getType() == SVDBItemType.Marker) {
				ret.add((SVDBMarkerItem)it_t);
			}
		}
		
		return ret;
	}

}
