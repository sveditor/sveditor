package net.sf.sveditor.core.tests.constraint_parser;

import java.io.FileInputStream;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBConstraint;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileFactory;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBScopeItem;
import net.sf.sveditor.core.expr.parser.SVConstraintExpr;
import net.sf.sveditor.core.expr.parser.SVConstraintSetExpr;
import net.sf.sveditor.core.expr.parser.SVExprDump;
import net.sf.sveditor.core.expr.parser.SVExprParseException;
import net.sf.sveditor.core.expr.parser.SVExprParser;
import junit.framework.TestCase;

public class SmokeTest extends TestCase {
	
	public void testBasics() {
		SVExprParser p = new SVExprParser();
		String constraint = "if (a == 5) {b inside {6, 7, [8:10]}; c == 7;} else if (b == 6) { c == 8 ; d == 10;}";
		StringInputStream in = new StringInputStream(constraint);
		SVExprDump dump = new SVExprDump(System.out);
		List<SVConstraintExpr> expr_l = null;
		
		try {
			expr_l = p.parse_constraint(in);
		} catch (SVExprParseException e) {
			e.printStackTrace();
		}
		
	}
	
	public void testReal() {
		SVDBFileFactory factory = new SVDBFileFactory();
		SVDBFile file = null;
		InputStream in = null;
		List<SVDBConstraint>	constraints = new ArrayList<SVDBConstraint>();
		List<List<SVConstraintExpr>> constraint_expr = new ArrayList<List<SVConstraintExpr>>();
		SVExprParser p = new SVExprParser();
		
		try {
			in = new FileInputStream("/home/ballance/try.svh");
			file = factory.parse(in, "try.svh");
		} catch (Exception e) {
			e.printStackTrace();
		}

		find_constraints(file, constraints);
		
		System.out.println("There are " + constraints.size() + " constraints");
		
		for (SVDBConstraint c : constraints) {
			System.out.println("[CONSTRAINT] " + c.getConstraintExpr());
			try {
				constraint_expr.add(p.parse_constraint(new StringInputStream(c.getConstraintExpr())));
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		
	}
	
	public static void find_constraints(SVDBScopeItem scope, List<SVDBConstraint> constraints) {
		for (SVDBItem it : scope.getItems()) {
			if (it.getType() == SVDBItemType.Constraint) {
				constraints.add((SVDBConstraint)it);
			} else if (it instanceof SVDBScopeItem) {
				find_constraints((SVDBScopeItem)it, constraints);
			}
		}
	}

}
