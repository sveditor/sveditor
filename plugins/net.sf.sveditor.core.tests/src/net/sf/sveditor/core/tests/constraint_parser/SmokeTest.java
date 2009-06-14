package net.sf.sveditor.core.tests.constraint_parser;

import java.util.List;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.constraint.parser.ConstraintParser;
import net.sf.sveditor.core.constraint.parser.ParseException;
import net.sf.sveditor.core.constraint.parser.SVConstraintExpr;
import net.sf.sveditor.core.constraint.parser.SVExprDump;
import junit.framework.TestCase;

public class SmokeTest extends TestCase {
	
	public void testBasics() {
		ConstraintParser p = new ConstraintParser();
		String constraint = "if (a == 5) {b == 6; c == 7;} else if (b == 6) { c == 8 ; d == 10;}";
		StringInputStream in = new StringInputStream(constraint);
		SVExprDump dump = new SVExprDump(System.out);
		List<SVConstraintExpr> expr_l = null;
		
		try {
			expr_l = p.parse(in);
		} catch (ParseException e) {
			e.printStackTrace();
		}
		
	}

}
