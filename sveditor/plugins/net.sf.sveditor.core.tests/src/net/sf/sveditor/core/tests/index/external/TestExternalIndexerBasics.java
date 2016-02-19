package net.sf.sveditor.core.tests.index.external;


import java.io.File;

import net.sf.sveditor.core.db.index.external.ExternalIndexerRunner;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestExternalIndexerBasics extends SVCoreTestCaseBase {
	
	public void testLaunch() {
		File argfile = new File(fTmpDir, "index.f");
		TestUtils.copy(
				"test.sv",
				argfile);
		File test_sv = new File(fTmpDir, "test.sv");
		TestUtils.copy(
				"module top;\n" +
				"endmodule",
				test_sv);
	
		long start, end;
		
		start = System.currentTimeMillis();
		ExternalIndexerRunner runner = ExternalIndexerRunner.allocRunner();
		end = System.currentTimeMillis();
		
		System.out.println("Spinup time: " + (end-start));

		start = System.currentTimeMillis();
		runner.build_index(argfile.toString(), null, null);
		end = System.currentTimeMillis();
		System.out.println("Build1 Time: " + (end-start));
		
		start = System.currentTimeMillis();
		runner.build_index(argfile.toString(), null, null);
		end = System.currentTimeMillis();
		System.out.println("Build2 Time: " + (end-start));
		
		runner.shutdown();
	}

}
