package net.sf.sveditor.core.tests.search;

import junit.framework.TestCase;

public class TestFindReferences extends TestCase {
	// Find references to class types
	// - variable declarations
	// - class extension
	// - typedef
	
	
	public void testFindExtensionRef() {
		String content =
			"class base;\n" +
			"endclass\n" +
			"\n" +
			"class extension extends base;\n" +
			"endclass\n"
			;
		
		
						
	}

}
