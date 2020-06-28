/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.constraint_parser;

import java.util.List;

import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBScopeItem;
import org.eclipse.hdt.sveditor.core.db.SVDBConstraint;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;

import junit.framework.TestCase;

public class SmokeTest extends TestCase {
	
	/*
	public void testBasics() {
		SVExprParser p = new SVExprParser();
		String constraint = "if (a == 5) {b inside {6, 7, [8:10]}; c == 7;} else if (b == 6) { c == 8 ; d == 10;}";
		StringInputStream in = new StringInputStream(constraint);
		SVExprDump dump = new SVExprDump(System.out);
		List<SVExpr> expr_l = null;
		
		try {
			expr_l = p.parse_constraint(new InputStreamTextScanner(in, ""));
		} catch (SVExprParseException e) {
			e.printStackTrace();
		}
		
	}
	
	public void testReal() {
		ISVDBFileFactory factory = SVCorePlugin.getDefault().createFileFactory(null);
		SVDBFile file = null;
		InputStream in = null;
		List<SVDBConstraint>	constraints = new ArrayList<SVDBConstraint>();
		List<List<SVExpr>> constraint_expr = new ArrayList<List<SVExpr>>();
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
				constraint_expr.add(p.parse_constraint(
						new StringTextScanner(c.getConstraintExpr())));
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		
	}
	 */
	
	public static void find_constraints(ISVDBScopeItem scope, List<SVDBConstraint> constraints) {
		for (ISVDBItemBase it : scope.getItems()) {
			if (it.getType() == SVDBItemType.Constraint) {
				constraints.add((SVDBConstraint)it);
			} else if (it instanceof ISVDBScopeItem) {
				find_constraints((ISVDBScopeItem)it, constraints);
			}
		}
	}

}
