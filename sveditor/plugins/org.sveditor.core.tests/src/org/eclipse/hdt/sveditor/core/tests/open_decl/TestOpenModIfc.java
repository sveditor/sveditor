/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.tests.open_decl;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBItem;
import org.eclipse.hdt.sveditor.core.db.SVDBItemType;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.db.SVDBMacroDef;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.open_decl.OpenDeclUtils;
import org.eclipse.hdt.sveditor.core.preproc.SVStringPreProcessor;
import org.eclipse.hdt.sveditor.core.scanutils.StringBIDITextScanner;

import org.eclipse.hdt.sveditor.core.tests.FileIndexIterator;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;
import org.eclipse.hdt.sveditor.core.tests.SVDBTestUtils;

public class TestOpenModIfc extends SVCoreTestCaseBase {
	
	public void testOpenModuleDecl() {
		LogHandle log = LogFactory.getLogHandle("testOpenModuleDecl");
		String doc =
			"module m1;\n" +
			"	wire A, B;\n" +
			"endmodule\n" +
			"\n" +
			"module m2;\n" +
			"	m1 u1();\n" +
			"endmodule\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, "testOpenModuleDecl");
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "m1", "m2");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("m1 u1");
		log.debug("index: " + idx);
		scanner.seek(idx+1);

		ISVDBIndexCache cache = FileIndexIterator.createCache(fCacheFactory);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file, 4, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.ModuleDecl, ret.get(0).first().getType());
		assertEquals("m1", SVDBItem.getName(ret.get(0).first()));

		LogFactory.removeLogHandle(log);
	}

	public void testOpenInterfaceDecl() {
		LogHandle log = LogFactory.getLogHandle("testOpenInterfaceDecl");
		String doc =
			"interface m1;\n" +
			"	wire A, B;\n" +
			"endinterface\n" +
			"\n" +
			"interface m2;\n" +
			"	m1 u1();\n" +
			"endinterface\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, "testOpenInterfaceDecl");
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "m1", "m2");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("m1 u1");
		log.debug("index: " + idx);
		scanner.seek(idx+1);

		ISVDBIndexCache cache = FileIndexIterator.createCache(fCacheFactory);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file, 4, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.InterfaceDecl, ret.get(0).first().getType());
		assertEquals("m1", SVDBItem.getName(ret.get(0).first()));

		LogFactory.removeLogHandle(log);
	}

	/** NOTE: this cannot be tested with the current StringBIDITextScanner()
	 * 
	 */
	public void disabled_testOpenModuleDeclwPreComment() {
		String testname = "testOpenModuleDeclwPreComment";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"module a(output o, input i);\n" +		// 1
			"	assign o = i;\n" +
			"endmodule\n" +
			"\n" +					
			"module b(output o, input i);\n" +		// 5
			"	// a.\n" +
			"	a a0(o, i);\n" +					// 7
			"endmodule\n" +
			"\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "a", "b");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("a a0");
//		log.debug("index: " + idx);
		scanner.seek(idx+1);

		ISVDBIndexCache cache = FileIndexIterator.createCache(fCacheFactory);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file, 7, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.ModuleDecl, ret.get(0).first().getType());
		assertEquals("a", SVDBItem.getName(ret.get(0).first()));

		LogFactory.removeLogHandle(log);
	}

	public void testStructFieldModuleScope() {
		String testname = "testStructFieldModuleScope";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"class MyClass;\n" +					// 1
			"	int aaaa;\n" +
			"endclass\n" +
			"\n" +
			"typedef struct packed {\n" + 			// 5
			"	logic [ 3:0] bbbb;\n" + 
			"} MyStruct;\n" +
			"\n" +
			"module m;\n" +
			"\n" +									// 10
			"initial begin\n" +
			"	MyStruct mystruct_obj;\n" +
			"	MyClass myclass_obj;\n" +
			"	$display(\"%d, %d\", mystruct_obj.bbbb, myclass_obj.aaaa);\n" +	 // 14
			"end\n" +
			"\n" +
			"endmodule\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "m");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("mystruct_obj.bbbb");
		log.debug("index: " + idx);
		scanner.seek(idx+"mystruct_obj.b".length());

		ISVDBIndexCache cache = FileIndexIterator.createCache(fCacheFactory);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);
		int lineno = 14;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file, lineno, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("bbbb", SVDBItem.getName(ret.get(0).first()));

		LogFactory.removeLogHandle(log);
	}

	public void testUnionFieldModuleScope() {
		String testname = "testUnionFieldModuleScope";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"class MyClass;\n" +					// 1
			"	int aaaa;\n" +
			"endclass\n" +
			"\n" +
			"typedef union {\n" + 			// 5
			"	logic [ 3:0] aaaa;\n" + 
			"	logic [ 3:0] bbbb;\n" + 
			"} MyUnion;\n" +
			"\n" +
			"module m;\n" +							// 10
			"\n" +									
			"initial begin\n" +
			"	MyUnion myunion_obj;\n" +
			"	MyClass myclass_obj;\n" +
			"	$display(\"%d, %d\", myunion_obj.bbbb, myclass_obj.aaaa);\n" +	 // 15
			"end\n" +
			"\n" +
			"endmodule\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "m");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("myunion_obj.bbbb");
		log.debug("index: " + idx);
		scanner.seek(idx+"myunion_obj.b".length());

		ISVDBIndexCache cache = FileIndexIterator.createCache(fCacheFactory);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);
		int lineno = 15;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file, lineno, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("bbbb", SVDBItem.getName(ret.get(0).first()));

		LogFactory.removeLogHandle(log);
	}

	public void testStructUnionFieldModuleScope() {
		String testname = "testStructUnionFieldModuleScope";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"class MyClass;\n" +					// 1
			"	int aaaa;\n" +
			"endclass\n" +
			"\n" +
			"typedef struct {\n" + 			// 5
			"	union {\n" +
			"		logic [ 3:0] aaaa;\n" + 
			"		logic [ 3:0] bbbb;\n" +
			"	} u;\n" +
			"} MyStruct;\n" +						// 10
			"\n" +
			"module m;\n" +
			"\n" +									
			"initial begin\n" +
			"	MyStruct mystruct_obj;\n" +			// 15
			"	MyClass myclass_obj;\n" +
			"	$display(\"%d, %d\", mystruct_obj.u.bbbb, myclass_obj.aaaa);\n" +	 // 17
			"end\n" +
			"\n" +
			"endmodule\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "m");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("mystruct_obj.u.bbbb");
		log.debug("index: " + idx);
		scanner.seek(idx+"mystruct_obj.u.bb".length());

		ISVDBIndexCache cache = FileIndexIterator.createCache(fCacheFactory);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);
		int lineno = 17;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file, lineno, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("bbbb", SVDBItem.getName(ret.get(0).first()));

		LogFactory.removeLogHandle(log);
	}
	
	public void testClassFieldModuleScope() {
		String testname = "testClassFieldModuleScope";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"class MyClass;\n" +					// 1
			"	int aaaa;\n" +
			"endclass\n" +
			"\n" +
			"typedef struct packed {\n" + 			// 5
			"	logic [ 3:0] bbbb;\n" + 
			"} MyStruct;\n" +
			"\n" +
			"module m;\n" +
			"\n" +									// 10
			"initial begin\n" +
			"	MyStruct mystruct_obj;\n" +
			"	MyClass myclass_obj;\n" +
			"	$display(\"%d, %d\", mystruct_obj.bbbb, myclass_obj.aaaa);\n" +	 // 14
			"end\n" +
			"\n" +
			"endmodule\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, testname);
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "m");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("myclass_obj.aaaa");
		log.debug("index: " + idx);
		scanner.seek(idx+"myclass_obj.a".length());

		ISVDBIndexCache cache = FileIndexIterator.createCache(fCacheFactory);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);
		int lineno = 14;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file, lineno, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("aaaa", SVDBItem.getName(ret.get(0).first()));

		LogFactory.removeLogHandle(log);
	}

	public void testModulePort() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module m(\n" +					// 1
			"	input		clk_i,\n" +
			"	input		rst_n\n" +
			");\n" +
			"\n" +							// 5	
			"	always @(posedge clk_i) begin\n" +
			"	end\n" +
			"\n" +
			"endmodule\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, getName());
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "m");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("posedge");
		fLog.debug("index: " + idx);
		scanner.seek(idx+"posedge cl".length());

		ISVDBIndexCache cache = FileIndexIterator.createCache(fCacheFactory);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);
		int lineno = 6;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file, lineno, scanner, target_index);
		
		fLog.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("clk_i", SVDBItem.getName(ret.get(0).first()));
		assertNotNull(ret.get(0).first().getLocation());
		assertEquals(2, SVDBLocation.unpackLineno(ret.get(0).first().getLocation()));
	}
	
	public void testModulePort_2() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module m(\n" +					// 1
			"	input		clk_i,\n" +
			"	input		rst_n\n" +
			");\n" +
			"\n" +							// 5	
			"	always @(posedge clk_i) begin\n" +
			"		rst_n <= 0;\n" +
			"	end\n" +
			"\n" +
			"endmodule\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, getName());
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "m");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("rst_n <=");
		fLog.debug("index: " + idx);
		scanner.seek(idx+1);

		ISVDBIndexCache cache = FileIndexIterator.createCache(fCacheFactory);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);
		int lineno = 6;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file, lineno, scanner, target_index);
		
		fLog.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("rst_n", SVDBItem.getName(ret.get(0).first()));
		assertNotNull(ret.get(0).first().getLocation());
		assertEquals(3, SVDBLocation.unpackLineno(ret.get(0).first().getLocation()));
	}	
	
	public void testModuleParameter() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module m #(parameter int P1=1, parameter int P2=2) (\n" +					// 1
			"	input		clk_i,\n" +
			"	input		rst_n\n" +
			");\n" +
			"\n" +							// 5	
			"	initial begin\n" +
			"		repeat (P1) begin\n" +
			"		end\n" +
			"	end\n" +
			"\n" +
			"endmodule\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, getName());
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "m");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("(P1)");
		fLog.debug("index: " + idx);
		scanner.seek(idx+1);


		int lineno = 7;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = 
				OpenDeclTests.runOpenDeclOp(fCacheFactory, file, lineno, scanner);
		
		fLog.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.ModIfcClassParam, ret.get(0).first().getType());
		assertEquals("P1", SVDBItem.getName(ret.get(0).first()));
		assertEquals(1, SVDBLocation.unpackLineno(ret.get(0).first().getLocation()));
		
		OpenDeclTests.validatePathToFile(ret.get(0).first());
	}	

	public void testModuleParameter_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"module m (\n" +					// 1
			"	input		clk_i,\n" +
			"	input		rst_n\n" +
			");\n" +
			"	parameter P1=1;\n" +							// 5	
			"	parameter P2=1;\n" +							// 6	
			"	initial begin\n" +
			"		repeat (P1) begin\n" +
			"		end\n" +
			"	end\n" +
			"\n" +
			"endmodule\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, getName());
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "m");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("(P1)");
		fLog.debug("index: " + idx);
		scanner.seek(idx+1);


		int lineno = 8;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = 
				OpenDeclTests.runOpenDeclOp(fCacheFactory, file, lineno, scanner);
		
		fLog.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("P1", SVDBItem.getName(ret.get(0).first()));
		assertEquals(5, SVDBLocation.unpackLineno(ret.get(0).first().getLocation()));
		
	}
	
	public void testOpenModuleTypeWithInstanceSameName() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"module foo (\n" + // 1
			"	input a,\n" +
			"	output b\n" +
			");\n" +
			"\n" +
			"	assign a = b;\n" +
			"endmodule\n" +
			"\n" +
			"module foo_test;\n" +
			"	// Open declaration works\n" + // 10
			"	foo foo1\n" +
			"	(\n" +
			"		.a(),\n" +
			"		.b()\n" +
			"	);\n" +
			"\n" +
			"	// Does not work\n" +
			"	foo foo\n" +				// 18
			"	(\n" +
			"		.a(),\n" +
			"		.b()\n" +
			"	);\n" +
			"endmodule\n" 
			;
		
		SVDBFile file = SVDBTestUtils.parse(doc, getName());
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "foo");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("foo foo");
		fLog.debug("index: " + idx);
		scanner.seek(idx+1);


		int lineno = 18;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = 
				OpenDeclTests.runOpenDeclOp(fCacheFactory, file, lineno, scanner);
		
		fLog.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.ModuleDecl, ret.get(0).first().getType());
		assertEquals("foo", SVDBItem.getName(ret.get(0).first()));
		assertEquals(1, SVDBLocation.unpackLineno(ret.get(0).first().getLocation()));
	}
	
	public void testOpenMacroRootedTaskPathDecl() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"`define TOP m2\n" + // 1
			"module s1;\n" +
			"	task t1;\n" +
			"	endtask\n" +
			"endmodule\n" +
			"module m1;\n" +
			"	s1		s1_i();\n" +
			"endmodule\n" +
			"\n" +
			"module m2;\n" + // 10
			"	m1		m1_i();\n" +
			"endmodule\n" +
			"module top;\n" +
			"	initial begin\n" +
			"		`TOP.m1_i.s1_i.t1();\n" + // 15
			"	end\n" +
			"endmodule\n"
			;
		SVStringPreProcessor p = new SVStringPreProcessor(
				new SVDBMacroDef("TOP", "m2")
				);

		SVDBFile file = SVDBTestUtils.parse(doc, getName());
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "m1", "m2");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("`TOP");
		fLog.debug("index: " + idx);
		scanner.seek(idx+"`TOP.m1_i.s1_i.t".length());

		ISVDBIndexCache cache = FileIndexIterator.createCache(fCacheFactory);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl_2(
				file, 15, scanner, p, target_index);
		
		fLog.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.Task, ret.get(0).first().getType());
		assertEquals("t1", SVDBItem.getName(ret.get(0).first()));

	}	
}

