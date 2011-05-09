/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
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

import junit.framework.TestCase;
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

public class TestOpenClass extends TestCase {
	
	public void testOpenVariableRef() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class foo;\n" +
			"endclass\n" +
			"\n" +
			"class bar;\n" +
			"    foo      m_foo;\n" +
			"\n" +
			"    function new();\n" +
			"        m_foo = 5;\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n" 
			;
		SVDBFile file = SVDBTestUtils.parse(doc, "testOpenVariableRef.svh");
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "foo", "bar");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("m_foo = 5;\n");
		System.out.println("index: " + idx);
		scanner.seek(idx+"m_f".length());

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
				file, 4, scanner, target_index);
		
		System.out.println(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("m_foo", SVDBItem.getName(ret.get(0).first()));
	}

	public void testOpenVariableDottedRef() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class foo;\n" +					// 1
			"	int		field_a;\n" +			// 2
			"endclass\n" +						// 3
			"\n" +								// 4
			"class bar;\n" +					// 5
			"    foo      m_foo;\n" +			// 6
			"\n" +								// 7
			"    function new();\n" +			// 8
			"        m_foo.field_a = 5;\n" +	// 9
			"    endfunction\n" +				// 10
			"\n" +								// 11
			"endclass\n" 						// 12
			;
		SVDBFile file = SVDBTestUtils.parse(doc, "testOpenVariableDottedRef.svh");
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "foo", "bar");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("m_foo.field_a = 5;\n");
//		System.out.println("index: " + idx);
		scanner.seek(idx+"m_foo.fie".length());

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
				file, 9, scanner, target_index);
		
//		System.out.println(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("field_a", SVDBItem.getName(ret.get(0).first()));
	}

	public void testOpenVariableExplicitThisDottedRef() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class foo;\n" +						// 1
			"	int		field_a;\n" +				// 2
			"endclass\n" +							// 3
			"\n" +									// 4
			"class bar;\n" +						// 5
			"    foo      m_foo;\n" +				// 6
			"\n" +									// 7
			"    function new();\n" +				// 8
			"        this.m_foo.field_a = 5;\n" +	// 9
			"    endfunction\n" +					// 10
			"\n" +									// 11
			"endclass\n" 							// 12
			;
		SVDBFile file = SVDBTestUtils.parse(doc, "testOpenVariableExplicitThisDottedRef.svh");
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "foo", "bar");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("m_foo.field_a = 5;\n");
//		System.out.println("index: " + idx);
		scanner.seek(idx+"m_foo.fie".length());

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
				file, 9, scanner, target_index);
		
//		System.out.println(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("field_a", SVDBItem.getName(ret.get(0).first()));
	}

	public void testOpenVariableDottedSuperRef() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class foo;\n" +					// 1
			"	int		field_a;\n" +			// 2
			"endclass\n" +						// 3
			"\n" +								// 4
			"class bar_s;\n" +					// 5
			"    foo      m_foo;\n" +			// 6
			"endclass\n" +						// 7
			"\n" +								// 8
			"class bar extends bar_s;\n" +		// 9
			"\n" +								// 10
			"    function new();\n" +			// 11
			"        m_foo.field_a = 5;\n" +	// 12
			"    endfunction\n" +				// 13
			"\n" +								// 14
			"endclass\n" 						// 15
			;
		SVDBFile file = SVDBTestUtils.parse(doc, "testOpenVariableDottedSuperRef.svh");
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "foo", "bar");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("m_foo.field_a = 5;\n");
//		System.out.println("index: " + idx);
		scanner.seek(idx+"m_foo.fie".length());

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
				file, 12, scanner, target_index);
		
//		System.out.println(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("field_a", SVDBItem.getName(ret.get(0).first()));
	}

	public void testOpenVariableExplicitDottedSuperRef() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class foo;\n" +						// 1
			"	int		field_a;\n" +				// 2
			"endclass\n" +							// 3
			"\n" +									// 4
			"class bar_s;\n" +						// 5
			"    foo      m_foo;\n" +				// 6
			"endclass\n" +							// 7
			"\n" +									// 8
			"class bar extends bar_s;\n" +			// 9
			"\n" +									// 10
			"    function new();\n" +				// 11
			"        super.m_foo.field_a = 5;\n" +	// 12
			"    endfunction\n" +					// 13
			"\n" +									// 14
			"endclass\n" 							// 15
			;
		
		SVDBFile file = SVDBTestUtils.parse(doc, "testOpenVariableExplicitDottedSuperRef.svh");
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "foo", "bar");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("m_foo.field_a = 5;\n");
//		System.out.println("index: " + idx);
		scanner.seek(idx+"m_foo.fie".length());

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
				file, 12, scanner, target_index);
		
//		System.out.println(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.VarDeclItem, ret.get(0).first().getType());
		assertEquals("field_a", SVDBItem.getName(ret.get(0).first()));
	}

	public void testOpenScopedClassReference() {
		LogHandle log = LogFactory.getLogHandle("testOpenScopedClassReference");
		SVCorePlugin.getDefault().enableDebug(false);
		String doc = 
			"package foo;\n" +
			"	class foo_c;\n" +
			"	endclass\n" +
			"endpackage\n" +
			"\n" +
			"\n" +
			"module bar;\n" +
			"	foo::foo_c		item;\n" +
			"endmodule\n"
			;
		SVDBFile file = SVDBTestUtils.parse(doc, "testOpenScopedClassReference.svh");
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "foo", "bar");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("foo::foo_c");
		log.debug("index: " + idx);
		scanner.seek(idx+"foo::fo".length());

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
				file, 4, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		LogFactory.removeLogHandle(log);
	}

	public void testOpenClassTypeRef() {
		LogHandle log = LogFactory.getLogHandle("testOpenClassTypeRef");
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class foo;\n" +
			"endclass\n" +
			"\n" +
			"class bar extends foo;\n" +
			"    foo      m_foo;\n" +
			"\n" +
			"    function new();\n" +
			"        m_foo = 5;\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n" 
			;
		SVDBFile file = SVDBTestUtils.parse(doc, "testOpenVariableRef.svh");
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "foo", "bar");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("extends foo");
		log.debug("index: " + idx);
		scanner.seek(idx+"extends f".length());

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
				file, 4, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.ClassDecl, ret.get(0).first().getType());
		assertEquals("foo", SVDBItem.getName(ret.get(0).first()));
	}

	public void testOpenIfcTypeRef() {
		LogHandle log = LogFactory.getLogHandle("testOpenClassTypeRef");
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"interface foo;\n" +
			"endinterface\n" +
			"\n" +
			"class bar;\n" +
			"    virtual foo      m_foo();\n" +
			"\n" +
			"    function new();\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n" 
			;
		SVDBFile file = SVDBTestUtils.parse(doc, "testOpenIfcTypeRef");
		SVDBTestUtils.assertNoErrWarn(file);
		SVDBTestUtils.assertFileHasElements(file, "foo", "bar");
		
		StringBIDITextScanner scanner = new StringBIDITextScanner(doc);
		int idx = doc.indexOf("virtual foo");
		log.debug("index: " + idx);
		scanner.seek(idx+"virtual f".length());

		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		List<Tuple<ISVDBItemBase, SVDBFile>> ret = OpenDeclUtils.openDecl(
				file, 4, scanner, target_index);
		
		log.debug(ret.size() + " items");
		assertEquals(1, ret.size());
		assertEquals(SVDBItemType.InterfaceDecl, ret.get(0).first().getType());
		assertEquals("foo", SVDBItem.getName(ret.get(0).first()));
	}

}
