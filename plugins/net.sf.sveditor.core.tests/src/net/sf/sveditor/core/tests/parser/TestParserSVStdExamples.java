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

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.parser.SVParseException;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SVDBTestUtils;

public class TestParserSVStdExamples extends TestCase {
	
	public void test_7_2_0_struct_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_7_2_0_struct_1", 
				"/data/parser/7.2.0_struct_1.svh", 
				new String[] {"c", "f", "IR"});
	}

	public void test_7_2_0_struct_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_7_2_0_struct_2", 
				"/data/parser/7.2.0_struct_2.svh", 
				new String[] {"c", "f", "IR"});
	}

	public void test_7_2_1_struct_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_7_2_1_struct_1", 
				"/data/parser/7.2.1_struct_1.svh", 
				new String[] {"c", "pack1", "pack2"});
	}

	public void test_7_2_1_struct_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_7_2_1_struct_2", 
				"/data/parser/7.2.1_struct_2.svh", 
				new String[] {"c", "s_atmcell"});
	}

	public void test_7_2_2_struct_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_7_2_2_struct_1", 
				"/data/parser/7.2.2_struct_1.svh", 
				new String[] {"c", "packet1", "p1", "pi"});
	}

	public void test_7_3_0_union_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_7_3_0_union_1", 
				"/data/parser/7.3.0_union_1.svh", 
				new String[] {"c", "num", "tagged_st", "ts"});
	}

	public void test_13_5_3_tf_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_13_5_3_tf_1", 
				"/data/parser/13.5.3_tf_1.svh", 
				new String[] {"c", "read", "do_something"});
	}

	public void test_13_5_3_tf_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_13_5_3_tf_2", 
				"/data/parser/13.5.3_tf_2.svh", 
				new String[] {"m", "n"});
	}

	public void test_13_5_4_tf_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_13_5_4_tf_1", 
				"/data/parser/13.5.4_tf_1.svh", 
				new String[] {"c"});
	}

	public void test_16_3_0_assert_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_3_0_assert_1", 
				"/data/parser/16.3.0_assert_1.svh", 
				new String[] {"c"});
	}
	
	public void test_16_3_0_assert_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_3_0_assert_2", 
				"/data/parser/16.3.0_assert_2.svh", 
				new String[] {"m"});
	}

	public void test_16_3_0_assert_3() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_3_0_assert_3", 
				"/data/parser/16.3.0_assert_3.svh", 
				new String[] {"m"});
	}

	public void test_16_4_2_assert_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_4_2_assert_1", 
				"/data/parser/16.4.2_assert_1.svh", 
				new String[] {"m"});
	}

	public void test_16_4_2_assert_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_4_2_assert_2", 
				"/data/parser/16.4.2_assert_2.svh", 
				new String[] {"m"});
	}

	public void test_16_4_2_assert_3() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_4_2_assert_3", 
				"/data/parser/16.4.2_assert_3.svh", 
				new String[] {"m"});
	}

	public void test_16_4_3_assert_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_4_3_assert_1", 
				"/data/parser/16.4.3_assert_1.svh", 
				new String[] {"m"});
	}

	public void test_16_4_3_assert_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_4_3_assert_2", 
				"/data/parser/16.4.3_assert_2.svh", 
				new String[] {"m"});
	}

	public void test_16_4_4_assert_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_4_4_assert_1", 
				"/data/parser/16.4.4_assert_1.svh", 
				new String[] {"m"});
	}

	public void test_16_4_4_assert_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_4_4_assert_2", 
				"/data/parser/16.4.4_assert_2.svh", 
				new String[] {"m"});
	}

	public void test_16_4_5_assert_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_4_5_assert_1", 
				"/data/parser/16.4.5_assert_1.svh", 
				new String[] {"fsm"});
	}

	public void test_16_6_0_assert_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_6_0_assert_1", 
				"/data/parser/16.6.0_assert_1.svh", 
				new String[] {"m"});
	}
	
	public void test_16_8_0_sequence_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_8_0_sequence_1", 
				"/data/parser/16.8.0_sequence_1.svh", 
				new String[] {"m"});
	}

	public void test_16_8_0_sequence_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_8_0_sequence_2", 
				"/data/parser/16.8.0_sequence_2.svh", 
				new String[] {"m"});
	}

	public void test_16_8_0_sequence_3() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_8_0_sequence_3", 
				"/data/parser/16.8.0_sequence_3.svh", 
				new String[] {"m"});
	}

	public void test_16_8_0_sequence_4() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_8_0_sequence_4", 
				"/data/parser/16.8.0_sequence_4.svh", 
				new String[] {"m"});
	}
	
	public void test_16_8_0_sequence_5() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_8_0_sequence_5", 
				"/data/parser/16.8.0_sequence_5.svh", 
				new String[] {"m"});
	}

	public void test_16_8_1_sequence_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_8_1_sequence_1", 
				"/data/parser/16.8.1_sequence_1.svh", 
				new String[] {"m"});
	}

	public void test_16_8_1_sequence_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_8_1_sequence_2", 
				"/data/parser/16.8.1_sequence_2.svh", 
				new String[] {"m"});
	}

	public void test_16_8_1_sequence_3() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_8_1_sequence_3", 
				"/data/parser/16.8.1_sequence_3.svh", 
				new String[] {"m"});
	}

	public void test_16_8_1_sequence_4() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_8_1_sequence_4", 
				"/data/parser/16.8.1_sequence_4.svh", 
				new String[] {"m"});
	}

	public void test_16_8_1_sequence_5() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_8_1_sequence_5", 
				"/data/parser/16.8.1_sequence_5.svh", 
				new String[] {"m"});
	}

	public void test_16_10_0_property_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_10_0_property_1", 
				"/data/parser/16.10.0_property_1.svh", 
				new String[] {"m"});
	}

	public void test_16_10_0_property_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_10_0_property_2", 
				"/data/parser/16.10.0_property_2.svh", 
				new String[] {"m"});
	}

	public void test_16_10_0_sequence_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_10_0_sequence_1", 
				"/data/parser/16.10.0_sequence_1.svh", 
				new String[] {"m"});
	}

	public void test_16_10_0_sequence_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_10_0_sequence_2", 
				"/data/parser/16.10.0_sequence_2.svh", 
				new String[] {"m"});
	}

	public void test_16_10_0_sequence_3() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_10_0_sequence_3", 
				"/data/parser/16.10.0_sequence_3.svh", 
				new String[] {"m"});
	}

	public void test_16_10_0_sequence_4() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_10_0_sequence_4", 
				"/data/parser/16.10.0_sequence_4.svh", 
				new String[] {"m"});
	}

	public void test_16_10_0_sequence_5() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_10_0_sequence_5", 
				"/data/parser/16.10.0_sequence_5.svh", 
				new String[] {"m"});
	}

	public void test_16_10_0_sequence_6() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_10_0_sequence_6", 
				"/data/parser/16.10.0_sequence_6.svh", 
				new String[] {"m"});
	}

	public void test_16_10_0_sequence_7() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_10_0_sequence_7", 
				"/data/parser/16.10.0_sequence_7.svh", 
				new String[] {"m"});
	}

	public void test_16_11_0_sequence_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_11_0_sequence_1", 
				"/data/parser/16.11.0_sequence_1.svh", 
				new String[] {"m"});
	}

	public void test_16_13_0_property_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_13_0_property_1", 
				"/data/parser/16.13.0_property_1.svh", 
				new String[] {"m"});
	}

	public void test_16_13_6_property_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_13_6_property_1", 
				"/data/parser/16.13.6_property_1.svh", 
				new String[] {"m"});
	}

	public void test_16_13_6_property_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_13_6_property_2", 
				"/data/parser/16.13.6_property_2.svh", 
				new String[] {"m"});
	}

	public void test_16_13_6_property_3() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_13_6_property_3", 
				"/data/parser/16.13.6_property_3.svh", 
				new String[] {"m"});
	}

	public void test_16_13_6_property_4() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_13_6_property_4", 
				"/data/parser/16.13.6_property_4.svh", 
				new String[] {"m"});
	}

	public void test_16_13_6_property_5() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_13_6_property_5", 
				"/data/parser/16.13.6_property_5.svh", 
				new String[] {"m"});
	}

	public void test_16_13_7_property_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_13_7_property_1", 
				"/data/parser/16.13.7_property_1.svh", 
				new String[] {"m"});
	}

	public void test_16_13_7_property_2() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_13_7_property_2", 
				"/data/parser/16.13.7_property_2.svh", 
				new String[] {"m"});
	}

	public void test_16_13_10_property_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_13_10_property_1", 
				"/data/parser/16.13.10_property_1.svh", 
				new String[] {"m"});
	}

	public void test_16_13_11_property_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_13_11_property_1", 
				"/data/parser/16.13.11_property_1.svh", 
				new String[] {"m"});
	}

	public void test_16_13_12_property_1() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		runTest("test_16_13_12_property_1", 
				"/data/parser/16.13.12_property_1.svh", 
				new String[] {"m"});
	}

	// TODO: 16.13.13

	private void runTest(String testname, String data, String exp_items[]) throws SVParseException {
		LogHandle log = LogFactory.getLogHandle(testname);
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		InputStream in = null;
		try {
			URL url = SVCoreTestsPlugin.getDefault().getBundle().getEntry(data);
			in = url.openStream();
		} catch (IOException e) {
			fail("Failed to open " + data + ": " + e.getMessage());
		}
		
		SVDBFile file = SVDBTestUtils.parse(log, in, data, markers).second();
		
		try {
			in.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		assertEquals(0, markers.size());
		SVDBTestUtils.assertFileHasElements(file, exp_items);
		
		LogFactory.removeLogHandle(log);
	}

}
