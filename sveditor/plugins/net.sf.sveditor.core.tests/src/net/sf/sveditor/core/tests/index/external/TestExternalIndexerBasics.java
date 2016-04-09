package net.sf.sveditor.core.tests.index.external;


import java.io.File;

import net.sf.sveditor.core.BundleUtils;
import net.sf.sveditor.core.db.index.external.ExternalIndexerRunner;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
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
	
	public void testParseUVM() {
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		TestUtils.copy(
				"+incdir+" + fTmpDir.getAbsolutePath() + "/uvm/src\n" +
				fTmpDir.getAbsolutePath() + "/uvm/src/uvm_pkg.sv",
				new File(fTmpDir, "uvm.f"));
		
		String argfile = fTmpDir.getAbsolutePath() + "/uvm.f";
	
		for (int out=0; out<4; out++) {
			ExternalIndexerRunner runner = ExternalIndexerRunner.allocRunner();

			long start, end;

			for (int i=0; i<32; i++) {
				start = System.currentTimeMillis();
				runner.build_index(argfile, null, null);
				end = System.currentTimeMillis();
				System.out.println("[" + (out+1) + "] Build " + (i+1) + " Time: " + (end-start));
			}

			runner.shutdown();
		}
	}
	
	public void testParseUVMRefFlow() {
		ExternalIndexerRunner runner = ExternalIndexerRunner.allocRunner();
	
		String argfile = 
				"c:/designs/sveditor-ref-designs/uvm_ref_flow_2013.05/run_dir/flist";
		
		long start, end;
		int out=0, i=0;
		
		start = System.currentTimeMillis();
		runner.build_index(argfile, null, null);
		end = System.currentTimeMillis();
		System.out.println("[" + (out+1) + "] Build " + (i+1) + " Time: " + (end-start));
		
		runner.shutdown();
	}

	public void testParseOpenSPARC() {
		ExternalIndexerRunner runner = ExternalIndexerRunner.allocRunner();
	
		String argfile = 
				"c:/designs/sveditor-ref-designs/OpenSPARCT2.1.3/design/sys/iop";
		
		long start, end;
		int out=0, i=0;
		
		start = System.currentTimeMillis();
		runner.build_index(argfile, null, null);
		end = System.currentTimeMillis();
		System.out.println("[" + (out+1) + "] Build " + (i+1) + " Time: " + (end-start));
		
		runner.shutdown();
	}

}
