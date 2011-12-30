package net.sf.sveditor.core.tests.hierarchy;

import java.util.List;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sf.sveditor.core.db.SVDBClassDecl;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.search.SVDBFindNamedClass;
import net.sf.sveditor.core.hierarchy.ClassHierarchyTreeFactory;
import net.sf.sveditor.core.hierarchy.HierarchyTreeNode;
import net.sf.sveditor.core.tests.IndexTestUtils;

public class HierarchyTests extends TestCase {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("HierarchyTests");
		suite.addTest(new TestSuite(HierarchyTests.class));
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
		
		HierarchyTreeNode h = tf.build(cls_l.get(0));
		assertEquals("c2_2", h.getName());
		h = h.getParent();
		assertEquals("c1", h.getName());
	}

}
