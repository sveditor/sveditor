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
		
		SVDBFile file = SVDBTestUtils.parse(log, in, data, markers);
		
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
