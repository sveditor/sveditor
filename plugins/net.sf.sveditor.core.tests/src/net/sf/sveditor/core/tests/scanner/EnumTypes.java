package net.sf.sveditor.core.tests.scanner;

import junit.framework.TestCase;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;

public class EnumTypes extends TestCase {
	
	public void testEnumTypedef() {
		String enum_defs = 
			"typedef enum { A=5, B='h70, C, D } letter_t;\n" +
			"\n\n" +
			"typedef int  cmd_t;\n" +
			"\n\n" +
			"typedef enum integer {I, J, K, L} letter2_t;\n" +
			"\n\n" +
			"class foobar;\n" +
			"    typedef enum { E, F, G, H } latter_t;\n" +
			"endclass\n" +
			"\n\n";
		StringInputStream in = new StringInputStream(enum_defs);
		
		SVDBFileFactory f = new SVDBFileFactory();
		
		SVDBFile file = f.parse(in, "enum_defs");
		
	}

}
