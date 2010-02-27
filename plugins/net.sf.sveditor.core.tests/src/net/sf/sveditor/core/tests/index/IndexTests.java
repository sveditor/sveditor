package net.sf.sveditor.core.tests.index;

import junit.framework.Test;
import junit.framework.TestSuite;
import net.sf.sveditor.core.tests.index.libIndex.WSArgFileIndexChanges;
import net.sf.sveditor.core.tests.index.libIndex.WSLibIndexFileChanges;

public class IndexTests extends TestSuite {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("IndexTests");
		suite.addTest(new TestSuite(WSLibIndexFileChanges.class));
		suite.addTest(new TestSuite(WSArgFileIndexChanges.class));
		
		return suite;
	}

}
