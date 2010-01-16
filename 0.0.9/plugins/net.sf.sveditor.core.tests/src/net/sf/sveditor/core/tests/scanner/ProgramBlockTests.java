package net.sf.sveditor.core.tests.scanner;

import junit.framework.TestCase;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;

public class ProgramBlockTests extends TestCase {
	

	protected void setUp() throws Exception {
		super.setUp();
	}
	
	public void testBasicProgramBlock() {
		StringInputStream in = new StringInputStream(
				"\n\n\n" +
				"class foo;\n" +
				"endclass\n" + 
				"program foobar;\n" +
				"endprogram\n" +
				"class foo_c;\n" +
				"endclass\n" +
				"\n\n\n\n");
		SVDBFileFactory f = new SVDBFileFactory();
		
		SVDBFile file = f.parse(in, "test");
		
		assertEquals("foo", file.getItems().get(0).getName());
		assertEquals("foobar", file.getItems().get(1).getName());
		assertEquals("foo_c", file.getItems().get(2).getName());
	}

	protected void tearDown() throws Exception {
		super.tearDown();
	}

}
