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


package org.eclipse.hdt.sveditor.core.tests.parser;

import org.eclipse.hdt.sveditor.core.tests.SVDBTestUtils;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;

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
		SVCorePlugin.getDefault().enableDebug(false);
		testTypeCastInFunction("		int i = int'(test_func());\n");
	}
	
	public void testIntegralTypeCast() {
		SVCorePlugin.getDefault().enableDebug(false);
		testTypeCastInFunction("		bit[5:0] i = 6'(test_func());\n");
	}
	
	public void testVoidCast() {
		testTypeCastInFunction("		void'(test_func());\n");
	}
	
	public void testConstTypeCast() {
		//const cast not supported by Questa at the moment it seems.
		SVCorePlugin.getDefault().enableDebug(false);
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
		SVDBFile file = SVDBTestUtils.parse(content, "testParameterizedFieldTypeInit");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t");
	}

	public void testAssociativeArrayInit() {
		String content = 
			"class t;\n" + 
			"	int str_int_map1[string] = '{default:null};\n" +
			"	int str_int_map2[string] = '{\"A\":5, \"B\":6};\n" +
			"   integer tab [string][string] = '{\"group1\": '{\"Peter\":20, \"Paul\":22}, \"group2\":'{\"Mary\":23, default:-1 }};\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, "testAssociativeArrayInit");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t", "str_int_map1", "str_int_map2", "tab");
	}

	public void testMultiDimAssociativeArrayInit() {
		String content = 
			"class t;\n" + 
			"	integer tab [string][string] = '{\"group1\": '{\"Peter\":20, \"Paul\":22}, \"group2\": '{\"Mary\":23, default:-1}};\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		SVDBFile file = SVDBTestUtils.parse(content, getName());

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t", "tab");
	}
	
	protected void testTypeCastInFunction(String castExpresson) {
		String content = 
			"class t;\n" +
			"	function f();\n" +
			castExpresson +
			"	endfunction\n" +
			"endclass\n"
			;
		SVDBFile file = SVDBTestUtils.parse(content, "testParameterizedFieldTypeInit");

		SVDBTestUtils.assertNoErrWarn(file);

		SVDBTestUtils.assertFileHasElements(file, "t", "f");
	}

}
