package net.sf.sveditor.core.tests.db;

import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class TestSVDBLocation extends SVCoreTestCaseBase {
	
	public void testBasics() {
		SVDBLocation l = new SVDBLocation(1, 20, 30);
		assertEquals(1, l.getFileId());
		assertEquals(20, l.getLine());
		assertEquals(30, l.getPos());
	}
	
	public void testLocationNegOne() {
		SVDBLocation l = new SVDBLocation(-1);
		assertEquals(-1, l.getFileId());
		assertEquals(-1, l.getLine());
		assertEquals(-1, l.getPos());
	}

}
