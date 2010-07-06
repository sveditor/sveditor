package net.sf.sveditor.core.tests.lexer;

import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.parser.ISVParser;
import net.sf.sveditor.core.parser.SVLexer;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.parser.SVParsers;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import junit.framework.TestCase;

public class TestClassItems extends TestCase {
	
	public void testClassFields() {
		String content = 
			"class __sv_builtin_covergroup_options;\n" +
			"	int 	weight;\n" + 
			"\n" +
			"	real 	goal;\n" +
			"\n" +
			"	string 	name;\n" +
			"\n" +
			"	string 	comment;\n" +
			"\n" +
			"	int		at_least;\n" +
			"\n" +
			"	bit		detect_overlap;\n" +
			"\n" +
			"	int		auto_bin_max;\n" +
			"\n" +
			"	bit		per_instance;\n" +
			"\n" +
			"	bit		cross_num_print_missing;\n" +
			"\n" +
			"endclass\n";

		final SVLexer lexer = new SVLexer();
		ISVParser parser = new ISVParser() {
			
			public void warning(String msg, int lineno) {}
			
			public SVParsers parsers() {
				return null;
			}
			
			public SVLexer lexer() {
				return lexer;
			}
			
			public boolean error_limit_reached() {
				return false;
			}
			
			public void error(SVParseException e) {}
			
			public void error(String msg) {}
			
			public SVDBLocation getLocation() {
				return null;
			}
		};
		lexer.init(parser, new StringTextScanner(content));
		
		while (lexer.peek() != null) {
			System.out.println("token: \"" + lexer.getImage() + "\"");
			lexer.eatToken();
		}
	}

}
