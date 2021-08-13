/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.tests.hierarchy;

import java.util.List;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBClassDecl;
import org.eclipse.hdt.sveditor.core.db.SVDBModIfcDecl;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindNamedClass;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindNamedPackage;
import org.eclipse.hdt.sveditor.core.expr_utils.SVExprContext;
import org.eclipse.hdt.sveditor.core.expr_utils.SVExprScanner;
import org.eclipse.hdt.sveditor.core.hierarchy.ClassHierarchyTreeFactory;
import org.eclipse.hdt.sveditor.core.hierarchy.HierarchyTreeNode;
import org.eclipse.hdt.sveditor.core.hierarchy.ModuleHierarchyTreeFactory;
import org.eclipse.hdt.sveditor.core.hierarchy.PackageHierarchyTreeFactory;
import org.eclipse.hdt.sveditor.core.scanutils.ITextScanner;
import org.eclipse.hdt.sveditor.core.scanutils.StringBIDITextScanner;
import org.eclipse.hdt.sveditor.core.scanutils.StringTextScanner;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import org.eclipse.hdt.sveditor.core.tests.IndexTestUtils;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;

public class HierarchyTests extends SVCoreTestCaseBase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("HierarchyTests");
		suite.addTest(new TestSuite(HierarchyTests.class));
		suite.addTest(new TestSuite(TestModuleHierarchy.class));
		return suite;
	}
	
	public void testClassHierarchy() {
		String doc = 
			"class c1;\n" +
			"endclass\n" +
			"\n" +
			"class c2_1 extends c1;\n" +
			"endclass\n" +
			"\n" +
			"class c2_2 extends c1;\n" +
			"endclass\n" +
			"\n"
			;
		String testname = "testClassHierarchy";
		ISVDBIndexIterator index_it = IndexTestUtils.buildIndex(doc, testname, fCacheFactory);
		ClassHierarchyTreeFactory tf = new ClassHierarchyTreeFactory(index_it);

		SVDBFindNamedClass cls_finder = new SVDBFindNamedClass(index_it);
		List<SVDBClassDecl> cls_l = cls_finder.findItem("c2_2");
		assertEquals(1, cls_l.size());
	
		// root, target
		HierarchyTreeNode h = tf.build(cls_l.get(0));
		
		assertEquals("c2_2", h.getName());
		h = h.getParent();
		assertNotNull(h);
		assertEquals("c1", h.getName());
	}

	public void disabled_testClassSubHierarchy() {
		String doc = 
			"class c1;\n" +
			"endclass\n" +
			"\n" +
			"class c2_1 extends c1;\n" +
			"endclass\n" +
			"\n" +
			"class c2_2_1 extends c2_1;\n" +
			"endclass\n" +
			"\n" +
			"class c2_2_2 extends c2_1;\n" +
			"endclass\n" +
			"\n"
			;
		String testname = "testClassHierarchy";
		ISVDBIndexIterator index_it = IndexTestUtils.buildIndex(doc, testname, fCacheFactory);
		ClassHierarchyTreeFactory tf = new ClassHierarchyTreeFactory(index_it);

		SVDBFindNamedClass cls_finder = new SVDBFindNamedClass(index_it);
		List<SVDBClassDecl> cls_l = cls_finder.findItem("c2_1");
		assertEquals(1, cls_l.size());
	
		// root, target
		HierarchyTreeNode h = tf.build(cls_l.get(0));
		
		assertEquals("c2_1", h.getName());
		
		HierarchyTreeNode c2_2_1 = null;
		HierarchyTreeNode c2_2_2 = null;
		
		for (HierarchyTreeNode c : h.getChildren()) {
			System.out.println("Child: " + c.getName());
			if (c.getName().equals("c2_2_1")) {
				c2_2_1 = c;
			} else if (c.getName().equals("c2_2_2")) {
				c2_2_2 = c;
			}
		}
		
		assertNotNull(c2_2_1);
		assertEquals("c2_2_1", c2_2_1.getName());
		assertNotNull(c2_2_2);
		assertEquals("c2_2_2", c2_2_2.getName());
	}

	public void disabled_testPackageHierarchy() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"package my_pkg;\n" +
			"	class c1;\n" +
			"	endclass\n" +
			"	class c2;\n" +
			"	endclass\n" +
			"endpackage\n" +
			"\n" +
			"class c2_1 extends c1;\n" +
			"endclass\n" +
			"\n" +
			"class c2_2_1 extends c2_1;\n" +
			"endclass\n" +
			"\n" +
			"class c2_2_2 extends c2_1;\n" +
			"endclass\n" +
			"\n"
			;
		String testname = getName();
		ISVDBIndexIterator index_it = IndexTestUtils.buildIndex(doc, testname, fCacheFactory);
		PackageHierarchyTreeFactory tf = new PackageHierarchyTreeFactory(index_it);
	
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		scanner.seek("package my".length());
		SVExprScanner			expr_scanner = new SVExprScanner();
		SVExprContext expr_ctxt = expr_scanner.extractExprContext(scanner, true);
	
		assertEquals("my_pkg", expr_ctxt.fLeaf);
		
		SVDBFindNamedPackage finder_p = new SVDBFindNamedPackage(index_it);
		List<SVDBDeclCacheItem> found_p = finder_p.find(expr_ctxt.fLeaf);
		
		assertEquals(1, found_p.size());
		
		HierarchyTreeNode root = tf.build(found_p.get(0));
		assertEquals(2, root.getChildren().size());
		
	}
	
	public static void runModuleHierarchyTest(
			String					testname,
			String					doc,
			String					top,
			ISVDBIndexCacheMgr		cache_mgr,
			String	...				paths) {
		ISVDBIndexIterator index_it = IndexTestUtils.buildIndex(doc, testname, cache_mgr);
		ModuleHierarchyTreeFactory tf = new ModuleHierarchyTreeFactory(index_it);

		SVDBFindNamedModIfcClassIfc mod_finder = new SVDBFindNamedModIfcClassIfc(index_it);
		List<SVDBDeclCacheItem> mod_l = mod_finder.findItems(top);
		assertEquals(1, mod_l.size());
	
		// root, target
		HierarchyTreeNode h = tf.build((SVDBModIfcDecl)mod_l.get(0).getSVDBItem());
		
		assertEquals(top, h.getName());
		
		for (String path : paths) {
			String path_split[] = path.split("\\.");
			for (int i=0; i<path_split.length; i++) {
				path_split[i] = path_split[i].trim();
			}
		
			HierarchyTreeNode n = find(h, path_split, 1);
			assertNotNull(n);
		}
	}
	
	public static HierarchyTreeNode find(HierarchyTreeNode parent, String path[], int idx) {
		HierarchyTreeNode target = null;
		
		for (HierarchyTreeNode c : parent.getChildren()) {
			if (c.getName().equals(path[idx])) {
				target = c;
				break;
			}
		}
		
		if (target == null) {
			StringBuilder path_str = new StringBuilder();
			StringBuilder avail_elems = new StringBuilder();
			for (HierarchyTreeNode c : parent.getChildren()) {
				avail_elems.append(c.getName());
				avail_elems.append(" ");
			}
			for (int i=0; i<=idx; i++) {
				path_str.append(path[i]);
				if (i+1 <= idx) {
					path_str.append(".");
				}
			}
			TestCase.fail("Failed to find path: " + path_str.toString() +
					" ; Available: " + avail_elems.toString());
		}

		if (idx+1 < path.length) {
			find(target, path, idx+1);
		}
		return target;
	}
}
