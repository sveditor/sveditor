/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.hierarchy;

import java.util.List;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.SVDBModIfcDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBFindNamedClass;
import net.sf.sveditor.core.db.search.SVDBFindNamedModIfcClassIfc;
import net.sf.sveditor.core.hierarchy.ClassHierarchyTreeFactory;
import net.sf.sveditor.core.hierarchy.HierarchyTreeNode;
import net.sf.sveditor.core.hierarchy.ModuleHierarchyTreeFactory;
import net.sf.sveditor.core.tests.IndexTestUtils;

public class HierarchyTests extends TestCase {
	
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
		ISVDBIndexIterator index_it = IndexTestUtils.buildIndex(doc, testname);
		ClassHierarchyTreeFactory tf = new ClassHierarchyTreeFactory(index_it);

		SVDBFindNamedClass cls_finder = new SVDBFindNamedClass(index_it);
		List<SVDBClassDecl> cls_l = cls_finder.find("c2_2");
		assertEquals(1, cls_l.size());
	
		// root, target
		HierarchyTreeNode h = tf.build(cls_l.get(0));
		
		assertEquals("c2_2", h.getName());
		h = h.getParent();
		assertNotNull(h);
		assertEquals("c1", h.getName());
	}

	public void testClassSubHierarchy() {
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
		ISVDBIndexIterator index_it = IndexTestUtils.buildIndex(doc, testname);
		ClassHierarchyTreeFactory tf = new ClassHierarchyTreeFactory(index_it);

		SVDBFindNamedClass cls_finder = new SVDBFindNamedClass(index_it);
		List<SVDBClassDecl> cls_l = cls_finder.find("c2_1");
		assertEquals(1, cls_l.size());
	
		// root, target
		HierarchyTreeNode h = tf.build(cls_l.get(0));
		
		assertEquals("c2_1", h.getName());
		
		HierarchyTreeNode c2_2_1 = null;
		HierarchyTreeNode c2_2_2 = null;
		
		for (HierarchyTreeNode c : h.getChildren()) {
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

	public static void runModuleHierarchyTest(
			String			testname,
			String			doc,
			String			top,
			String	...		paths) {
		ISVDBIndexIterator index_it = IndexTestUtils.buildIndex(doc, testname);
		ModuleHierarchyTreeFactory tf = new ModuleHierarchyTreeFactory(index_it);

		SVDBFindNamedModIfcClassIfc mod_finder = new SVDBFindNamedModIfcClassIfc(index_it);
		List<ISVDBChildItem> mod_l = mod_finder.find(top);
		assertEquals(1, mod_l.size());
	
		// root, target
		HierarchyTreeNode h = tf.build((SVDBModIfcDecl)mod_l.get(0));
		
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
