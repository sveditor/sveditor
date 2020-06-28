/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.tests.SVDBTestUtils;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.parser.SVParseException;

import junit.framework.TestCase;

public class TestParserClockingBlock extends TestCase {

	public void testClocking_LRM_Ex1() {
		String doc =
			"module test;\n" +
			"	clocking ck1 @(posedge clk);\n" +
			"		default input #1step output negedge;\n" +
			"	endclocking\n" +
			"endmodule\n";
		
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testClocking_LRM_Ex1");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "test");
	}
	
	public void testClocking_DR() {
		String doc = 
			"interface control_if;\n" +
			"	clocking cb @(posedge clk);\n" +
			"	endclocking : cb\n" +
			"endinterface : control_if\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, "testClocking_DR");
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "control_if");
	}

	public void testClockingSameLine_DR() {
		String testname = "testClockingSameLine_DR";
		String doc = 
			"interface control_if;\n" +
			"	clocking mon_cb @(posedge clk); endclocking\n" +
			"\n" +
			"	clocking cb @(posedge clk); endclocking\n" +
			"endinterface : control_if\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "control_if");
	}	

	public void testClockingBlockInout() {
		String testname = "testClockingSameLine_DR";
		String doc = 
			"module clk_blk_out;\n" +
			"	clocking mst_cb @(posedge clk);\n" +
			"		inout      confused;\n" +
			"	endclocking : mst_cb\n" +
			"endmodule\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "clk_blk_out");
	}	

	public void testClockingBlockOutput() {
		String testname = "testClockingSameLine_DR";
		String doc = 
			"module clk_blk_out;\n" +
			"	clocking mst_cb @(posedge clk);\n" +
			"		output     wr;\n" +
			"		output     addr;\n" +
			"		output     wdata;\n" +
			"		input      ready;\n" +
			"	endclocking : mst_cb\n" +
			"endmodule\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "clk_blk_out");
	}	

	public void testClockingBlockProperty() {
		String doc = 
			"interface my_if (\n" +
			"	input       clk,\n" +
			"	input       reset,\n" +
			"	inout [1:0] cmd_val,\n" +
			"	inout       wr_ptr_init\n" +
			");\n" +
			"	clocking my_cb @(posedge clk);\n" +
			"		default input #1step output #0;\n" +
			"		input cmd_val;\n" +
			"		input reset;\n" +
			"		input wr_ptr_init;\n" +
			"\n" +
			"	property reset_legal; // <-- ISSUE\n" +
			"		(!((reset ===1 ) && (cmd_val[0] || cmd_val[1] || wr_ptr_init)));\n" +
			"	endproperty\n" +
			"\n" +
			"	endclocking\n" +
			"endinterface\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, getName());
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "my_if");
	}	

	public void testClockingWaitCycle() {
		String testname = getName();
		String doc = 
			"interface my_if (\n" +
			"	input       clk,\n" +
			"	input       reset,\n" +
			"	inout [1:0] cmd_val,\n" +
			"	inout       wr_ptr_init\n" +
			");\n" +
			"	clocking my_cb @(posedge clk);\n" +
//			"		default input #1step output #0;\n" +
			"		input cmd_val;\n" +
			"		input reset;\n" +
			"		input wr_ptr_init;\n" +
			"	endclocking\n" +
			"\n" +
			"\n" +
			"	initial begin\n" +
			"		##0;\n" +
			"	end\n" +
			"\n" +
			"\n" +
			"endinterface\n"
			;

		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "my_if");
	}
	
	public void testClockingBlockNamedDefault() throws SVParseException {
		String doc =
			"module processor;\n" +
			"	clocking busA @(posedge clk1); endclocking\n" +
			"	clocking busB @(negedge clk2); endclocking\n" +
			"\n" +
			"module cpu( interface y );\n" +
			"	default clocking busA ;\n" +
			"	initial begin\n" +
			"		## 5; // use busA => (posedge clk1)\n"  +
			"end\n" +
			"endmodule\n" +
			"endmodule\n"
			;
		
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(doc, getName());
		
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "processor");
	}
}
