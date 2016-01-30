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
		
		ExternalIndexerRunner runner = new ExternalIndexerRunner();
		runner.run(argfile.toString(), null, null);
	}

}
