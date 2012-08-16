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
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.tests.SVDBTestUtils;
import junit.framework.TestCase;

public class TestTypeDeclarations extends TestCase {
	
	public void testParameterizedFieldType() {
		String content = 
			"class t;\n" + 
			"	item_t #(P) item;\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testParameterizedFieldType");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t", "item");
	}

	public void testParameterizedFieldTypeInit() {
		String content = 
			"class t;\n" + 
			"	item_t #(P) item = item_t #(P)::get();\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testParameterizedFieldTypeInit");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t", "item");
	}

	public void testParameterizedFieldTypeStaticInit() {
		String content = 
			"class t;\n" + 
			"	item_t #(P) item = item_t::get();\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testParameterizedFieldTypeInit");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t", "item");
	}

	public void testTypeParameterizedClass() {
		testTypeCastInFunction("		item_t #(int unsigned)::set(5);\n");
	}

	public void testBuiltinTypeCast() {
		testTypeCastInFunction("		int i = int'(test_func());\n");
	}
	
	public void testIntegralTypeCast() {
		testTypeCastInFunction("		bit[5:0] i = 6'(test_func());\n");
	}
	
	public void testVoidCast() {
		testTypeCastInFunction("		void'(test_func());\n");
	}
	
	public void testConstTypeCast() {
		//const cast not supported by Questa at the moment it seems.
		testTypeCastInFunction("		int i = const'(test_func());\n");
	}

	public void testParameterizedFieldInit() {
		String content = 
			"class t;\n" + 
			"	function foo;\n" +
			"		item_t #(P)::item = 5;\n" +
			"	endfunction\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testParameterizedFieldTypeInit");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t");
	}

	public void testAssociativeArrayInit() {
		String content = 
			"class t;\n" + 
			"	int str_int_map1[string] = '{default:null};\n" +
			"	int str_int_map2[string] = '{\"A\":5, \"B\":6};\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testAssociativeArrayInit");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t", "str_int_map1", "str_int_map2");
	}
	
	protected void testTypeCastInFunction(String castExpresson) {
		String content = 
			"class t;\n" +
			"	function f();\n" +
			castExpresson +
			"	endfunction\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testParameterizedFieldTypeInit");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t", "f");
	}

}
