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


package org.eclipse.hdt.sveditor.core.tests.content_assist;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;

public class TestArrayContentAssist extends SVCoreTestCaseBase {
	
	public void testMultiple() {
		String doc_arr[] = {
			// Document 0
			"class elem_t;\n" +
			"    int my_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_t			m_queue_item[$];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item.<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n",
			// Document 1
			"class elem_c;\n" +
			"    int     m_int_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_c		m_queue_item[$];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item[0].<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n",
			// Document 2
			"class elem_t;\n" +
			"    int my_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_t			m_queue_item[];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item.<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n",
			// Document 3
			"class elem_c;\n" +
			"    int     m_int_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_c		m_queue_item[];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item[0].<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
		};
		
		String [] exp_arr[] = {
				new String[] { "size", "insert", "delete", "pop_front",
						"pop_back", "push_front", "push_back"},
				new String[] {"m_int_field"},
				new String[] {"size"},
				new String[] {"m_int_field"}				
		};

		SVCorePlugin.getDefault().enableDebug(false);
		for (int i=0; i<doc_arr.length; i++) {
			ContentAssistTests.runTest(
					this,
					doc_arr[i], 
					exp_arr[i]);
		}
	}

	public void testQueueFunctions() {
		String doc =
			"class elem_t;\n" +
			"    int my_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_t			m_queue_item[$];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item.<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		
		ContentAssistTests.runTest(
				this,
				doc,
				"size", "insert", "delete", "pop_front",
				"pop_back", "push_front", "push_back");
	}

	public void testQueueElemItems() {
		String doc =
			"class elem_c;\n" +
			"    int     m_int_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_c		m_queue_item[$];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item[0].<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		ContentAssistTests.runTest(this, doc, "m_int_field");
	}

	public void testArrayFunctions() {
		String doc =
			"class elem_t;\n" +
			"    int my_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_t			m_queue_item[];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item.<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		ContentAssistTests.runTest(this, doc, "size");
	}

	public void testArrayElemItems() {
		String doc =
			"class elem_c;\n" +
			"    int     m_int_field;\n" +
			"endclass\n" +
			"\n" +
			"class my_class1;\n" +							// 1
			"		elem_c		m_queue_item[];\n" +		
			"\n" +
			"    function void my_func();\n" +
			"        m_queue_item[0].<<MARK>>\n" +
			"    endfunction\n" +
			"\n" +
			"endclass\n"
			;
		SVCorePlugin.getDefault().enableDebug(false);
		ContentAssistTests.runTest(this, doc, "m_int_field");
	}

}
