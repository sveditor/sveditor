package net.sf.sveditor.core.tests.index;

import junit.framework.Test;
import junit.framework.TestSuite;
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
		suite.addTest(new TestSuite(TestIndexParse.class));
		
		return suite;
	}

}
