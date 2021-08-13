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


package org.eclipse.hdt.sveditor.core.tests.index;

import java.util.ArrayList;
import java.util.List;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import org.eclipse.hdt.sveditor.core.tests.objects.ObjectsTests;

import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindDefaultNameMatcher;

public class IndexTests extends TestSuite {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("IndexTests");
//		suite.addTest(new TestSuite(WSLibIndexFileChanges.class));
//		suite.addTest(new TestSuite(WSArgFileIndexChanges.class));
//		suite.addTest(new TestSuite(SrcCollectionBasics.class));
		suite.addTest(new TestSuite(TestBuiltinIndex.class));
		suite.addTest(new TestSuite(TestDeclCache.class));
		suite.addTest(new TestSuite(TestIndexMissingIncludeDefine.class));
		suite.addTest(new TestSuite(TestGlobalDefine.class));
		suite.addTest(new TestSuite(TestVmmBasics.class));
		suite.addTest(new TestSuite(TestOvmBasics.class));
		suite.addTest(new TestSuite(TestUvmBasics.class));
		suite.addTest(new TestSuite(TestUvmPrimer.class));
		suite.addTest(new TestSuite(TestIndexParse.class));
		suite.addTest(new TestSuite(TestArgFileIndex.class));
//		suite.addTest(new TestSuite(TestArgFileIndexErrors.class));
//		suite.addTest(new TestSuite(TestArgFileParseAPI.class));
//		suite.addTest(new TestSuite(TestIndexPersistance.class));
		suite.addTest(new TestSuite(TestOpencoresProjects.class));
		suite.addTest(new TestSuite(TestCrossIndexReferences.class));
		suite.addTest(new TestSuite(TestIndexFileRefs.class));
//		suite.addTest(new TestSuite(TestThreadedSourceCollectionIndex.class));
		suite.addTest(new TestSuite(ObjectsTests.class));
		
		return suite;
	}

	/*
	public static List<SVDBMarker> getErrorsWarnings(ISVDBIndexIterator index_it) {
		ISVDBItemIterator it = index_it.getItemIterator(new NullProgressMonitor());
		List<SVDBMarker> ret = new ArrayList<SVDBMarker>();
		
		while (it.hasNext()) {
			ISVDBItemBase it_t = it.nextItem();
			if (it_t.getType() == SVDBItemType.Marker) {
				ret.add((SVDBMarker)it_t);
			}
		}
		
		return ret;
	}
	 */
	public static void assertContains(ISVDBIndexIterator index_it, String name) {
		assertContains(index_it, name, null);
	}
	
	public static void assertContains(ISVDBIndexIterator index_it, String name, SVDBItemType type) {
		List<SVDBDeclCacheItem> result = index_it.findGlobalScopeDecl(new NullProgressMonitor(), name, 
				SVDBFindDefaultNameMatcher.getDefault());
		TestCase.assertEquals("Failed to find " + name, 1, result.size());
		SVDBDeclCacheItem item_c = result.get(0);
		TestCase.assertNotNull("failed to get item " + item_c.getName(), item_c.getSVDBItem());
		if (type != null) {
			TestCase.assertEquals("item is not of type " + type, type, item_c.getSVDBItem().getType());
		}
	}

	public static void assertDoesNotContain(ISVDBIndexIterator index_it, String name) {
		List<SVDBDeclCacheItem> result = index_it.findGlobalScopeDecl(new NullProgressMonitor(), name, 
				SVDBFindDefaultNameMatcher.getDefault());
		TestCase.assertEquals("Unexpectedly found " + name, 0, result.size());
	}
	
	public static boolean WaitForEvent() {
		return WaitForEvent(10000);
	}

	public static boolean WaitForEvent(int timeout) {
		final List<Integer> events = new ArrayList<Integer>();
		
		IResourceChangeListener l = new IResourceChangeListener() {
			
			@Override
			public void resourceChanged(IResourceChangeEvent event) {
				synchronized (events) {
					events.add(1);
					events.notifyAll();
				}
			}
		};
		
		try {
			ResourcesPlugin.getWorkspace().addResourceChangeListener(l);

			try {
				synchronized (events) {
					events.wait(timeout);
				}
			} catch (InterruptedException e) {
				System.out.println("Interrupted");
			}
		} finally {
			ResourcesPlugin.getWorkspace().removeResourceChangeListener(l);
		}
		
		return (events.size() > 0);
	}
}

