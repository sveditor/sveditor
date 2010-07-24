package net.sf.sveditor.core.tests.srcgen;

import net.sf.sveditor.core.db.index.SVDBIndexCollectionMgr;
import net.sf.sveditor.core.tests.SVDBStringDocumentIndex;
import junit.framework.Test;
import junit.framework.TestSuite;

public class SrcGenTests extends TestSuite {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("SrcGenTests");
		suite.addTest(new TestSuite(TestNewClassGen.class));
		suite.addTest(new TestSuite(TestMethodGenerator.class));
		
		return suite;
	}
	
	public static SVDBIndexCollectionMgr createIndex(String doc) {
		SVDBIndexCollectionMgr index_mgr = new SVDBIndexCollectionMgr("GLOBAL");
		index_mgr.addPluginLibrary(new SVDBStringDocumentIndex(doc));
		
		return index_mgr;
	}

}
