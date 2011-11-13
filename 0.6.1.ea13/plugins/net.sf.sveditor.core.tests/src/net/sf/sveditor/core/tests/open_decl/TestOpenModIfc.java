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


package net.sf.sveditor.core.tests.open_decl;

import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.open_decl.OpenDeclUtils;
import net.sf.sveditor.core.scanutils.StringBIDITextScanner;
import net.sf.sveditor.core.tests.FileIndexIterator;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import junit.framework.TestCase;

public class TestOpenModIfc extends TestCase {
	
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

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
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

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
				file, 4, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.InterfaceDecl, ret.get(0).first().getType());
		assertEquals("m1", SVDBItem.getName(ret.get(0).first()));

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

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		int lineno = 14;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
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

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		int lineno = 15;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
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

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		int lineno = 17;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
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

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		int lineno = 14;
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
				file, lineno, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("aaaa", SVDBItem.getName(ret.get(0).first()));

		LogFactory.removeLogHandle(log);
	}

}

