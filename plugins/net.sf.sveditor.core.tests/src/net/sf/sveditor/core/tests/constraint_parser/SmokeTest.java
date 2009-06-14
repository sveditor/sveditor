package net.sf.sveditor.core.tests.constraint_parser;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.constraint.parser.ConstraintParser;
import net.sf.sveditor.core.constraint.parser.ParseException;
import junit.framework.TestCase;

public class SmokeTest extends TestCase {
	
	public void testBasics() {
		ConstraintParser p = new ConstraintParser();
		String constraint = "a == 5";
		StringInputStream in = new StringInputStream(constraint);
		
		try {
			p.parse(in);
		} catch (ParseException e) {
			e.printStackTrace();
		}
	}

}
