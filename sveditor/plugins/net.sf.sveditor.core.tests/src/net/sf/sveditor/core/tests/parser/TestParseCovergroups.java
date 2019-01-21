/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.parser.SVParseException;
import junit.framework.TestCase;

public class TestParseCovergroups extends TestCase {

	  public void testCovergroup() throws SVParseException {
		String testname = "testTransitionBins";
	    SVCorePlugin.getDefault().enableDebug(false);
	    String doc =
	      "class c;\n" +
	      " covergroup foobar;\n" +
	      "   foo_cp : coverpoint (foo);\n" +
	      "   foo2_cp : coverpoint foo2;\n" +
	      "   foo_cross : cross foo_cp, foo2_cp {\n" +
	      "     ignore_bins foo = binsof(foo_cp) intersect {0};\n" +
	      "   }\n" +
	      "   foo_cross_not_bins : cross foo_cp, foo2_cp {\n" +
	      "     ignore_bins foo = !binsof(foo_cp) intersect {0};\n" +
	      "   }\n" +
	      " endgroup\n" +
	      "endclass\n"
	      ;

		ParserTests.runTestStrDoc(testname, doc, new String[] {"c","foobar"});
	  }

	  public void testCovergroupInPackage() throws SVParseException {
		  String testname = "testTransitionBins";
		  SVCorePlugin.getDefault().enableDebug(false);
		  String doc = 
				  "package pkg;\n" +
						  "	covergroup cg;\n" +
						  "		a_cp : coverpoint a {\n" +
						  "			bins a_bins[] = (0 => 0,1), (1 => 0);\n" +
						  "		}\n" +
						  "	endgroup\n" +
						  "endpackage\n"
						  ;
		  ParserTests.runTestStrDoc(testname, doc, new String[] {"pkg","cg"});
	  }


	public void testTransitionBins() throws SVParseException {
		String testname = "testTransitionBins";
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"class c;\n" +
			"	covergroup cg;\n" +
			"		a_cp : coverpoint a {\n" +
			"			bins a_bins[] = (0 => 0,1), (1 => 0);\n" +
			"		}\n" +
			"	endgroup\n" +
			"endclass\n"
			;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"c","cg"});
	}

	public void testTransitionBins2() throws SVParseException {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"class c;\n" +
			"	covergroup cg;\n" +
			"		a_cp : coverpoint a {\n" +
			"			bins a_bins[] = (0,1,2 => 1,2,3 => 2,3,4);\n" +
			"			bins mod5[] = {[1000:2000]} with (item % 5 == 0);\n" +	// Bug #470 bins usage
			"		}\n" +
			"	endgroup\n" +
			"endclass\n"
			;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"c","cg"});
	}

	public void testTransitionBins3() throws SVParseException {
		String testname = getName();
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"class c;\n" +
			"	covergroup op_cov;\n" +
			"		coverpoint op_set {\n" +
			"			bins single_cycle[] = {[add_op : xor_op], rst_op,no_op};\n" +
		    "			bins multi_cycle = {mul_op};\n" +
		    "			bins opn_rst[] = ([add_op:mul_op] => rst_op);\n" +
		    "			bins rst_opn[] = (rst_op => [add_op:mul_op]);\n" +
		    "			bins sngl_mul[] = ([add_op:xor_op],no_op => mul_op);\n" +
		    "			bins mul_sngl[] = (mul_op => [add_op:xor_op], no_op);\n" +
		    "			bins twoops[] = ([add_op:mul_op] [* 2]);\n" +
		    "			bins manymult = (mul_op [* 3:5]);\n" +
		    "		}\n" +
		    "	endgroup\n" +
			"endclass\n"
			;
		ParserTests.runTestStrDoc(testname, doc, new String[] {"c", "op_cov"});
	}
	
	public void testIndexedBinsOf() throws SVParseException {
	    SVCorePlugin.getDefault().enableDebug(false);
	    String doc =
	      "class c;\n" +
	      " covergroup foobar;\n" +
	      "   foo_cp : coverpoint (foo);\n" +
	      "   foo2_cp : coverpoint foo2;\n" +
	      "   foo_cross : cross foo_cp, foo2_cp {\n" +
	      "		bins foo_val = binsof(foo_cp.foo[1]);\n" +
	      "   }\n" +
	      " endgroup\n" +
	      "endclass\n"
	      ;

		ParserTests.runTestStrDoc(getName(), doc, new String[] {"c","foobar"});
	}

	public void testCrossWithExpr() throws SVParseException {
	    SVCorePlugin.getDefault().enableDebug(false);
	    String doc =
			"class c;\n" +
			"  covergroup foo;\n" +
			"    IRQ_number_cvp__Isnon_Secure_cvp__cross: cross IRQ_number_cvp, Isnon_Secure_cvp {\n" + 
			"        ignore_bins ignore_x_values_higher_than_y = IRQ_number_cvp__Isnon_Secure_cvp__cross with (IRQ_number_cvp < 32) iff (i==32);\n" + 
			"    }\n" + 
			"\n" + 
			"    IRQ_number_cvp__IsPriveleged_cvp__cross: cross IRQ_number_cvp, IsPriveleged_cvp {   \n" + 
			"        ignore_bins ignore_x_values_higher_than_y = IRQ_number_cvp__IsPriveleged_cvp__cross with (IRQ_number_cvp < 32) iff (i==32);\n" + 
			"    }\n" +
			"  endgroup\n" +
			"endclass\n"
			;
		ParserTests.runTestStrDoc(getName(), doc, new String[] {"c","foo"});
	}
}
