package net.sf.sveditor.core.tests.parser;

import junit.framework.TestCase;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBModIfcClassDecl;
import net.sf.sveditor.core.parser.ParserSVDBFileFactory;
import net.sf.sveditor.core.parser.SVParseException;

public class TestParseDataTypes extends TestCase {
	
	public void testTypedefVirtual() throws SVParseException {
		String content =
			"class foobar;\n" +
			"    typedef virtual my_if #(FOO, BAR, BAZ) my_if_t;\n" +
			"\n" +
			"endclass\n";
		ParserSVDBFileFactory parser = new ParserSVDBFileFactory(null);
		parser.init(new StringInputStream(content), "test");
		
		SVDBModIfcClassDecl cls =
			parser.parsers().classParser().parse(0);
		
		for (SVDBItem it : cls.getItems()) {
			System.out.println("it " + it.getType() + " " + it.getName());
		}
	}

}
