package net.sf.sveditor.core.tests.templates.sim;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tests.ISimToolchain;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.SimBuildSpec;
import net.sf.sveditor.core.tests.SimRunSpec;
import net.sf.sveditor.core.tests.SimToolchainUtils;
import net.sf.sveditor.core.tests.TestNullIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;
import net.sf.sveditor.svt.core.templates.TemplateFSFileCreator;
import net.sf.sveditor.svt.core.templates.TemplateInfo;
import net.sf.sveditor.svt.core.templates.TemplateParameterProvider;
import net.sf.sveditor.svt.core.templates.TemplateProcessor;
import net.sf.sveditor.svt.core.templates.TemplateRegistry;
import net.sf.sveditor.svt.core.text.TagProcessor;

public class TestUVMTemplates extends TestCase {
	private LogHandle				fLog;
	private File					fTmpDir;

	@Override
	protected void setUp() throws Exception {
		fLog = LogFactory.getLogHandle(getName());
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		if (fTmpDir != null && fTmpDir.isDirectory()) {
			TestUtils.delete(fTmpDir);
		}
		
		LogFactory.removeLogHandle(fLog);
	}
	
	public void testUVMAgent_Questa() throws IOException {
		core_testUVMAgent(SimToolchainUtils.QUESTA);
	}

	private void core_testUVMAgent(String sim) throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		TemplateRegistry rgy = new TemplateRegistry(true);
		TemplateInfo tmpl = rgy.findTemplate("org.uvmworld.uvm.uvm_agent");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		assertNotNull(tmpl);
		TagProcessor proc = new TagProcessor();
		TemplateParameterProvider p = new TemplateParameterProvider();
		p.setTag("name", "simple");
		p.setTag("file_header", "");
		p.setTag("file_footer", "");
		proc.addParameterProvider(p);
		
		TemplateFSFileCreator out_sp = new TemplateFSFileCreator(
				new File(fTmpDir, "simple_agent"));
		TemplateProcessor tp = new TemplateProcessor(out_sp);
		
		tp.process(tmpl, proc);

		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);		

		SVDBIndexRegistry i_rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		i_rgy.init(new TestNullIndexCacheFactory());

		// Create stub testbench and environment
		for (String file : new String[] { 
				"simple_agent_tb.sv",
				"simple_agent_test.svh",
				"simple_agent_test_seq_item.svh",
				"simple_agent_test_seq.svh",
				"simple_agent_test_subscriber.svh"}) {
			utils.copyBundleFileToFS("/data/templates/uvm_agent_env/" + file, fTmpDir);
		}

		File sim_log = new File(fTmpDir, "sim.log");
		SimBuildSpec build_spec = new SimBuildSpec();
		
		build_spec.addIncDir("./uvm/src");
		build_spec.addFile("./uvm/src/uvm_pkg.sv");
		build_spec.addIncDir("./simple_agent");
		build_spec.addFile("./simple_agent/simple_agent_pkg.sv");
		
		build_spec.addIncDir(".");
		build_spec.addFile("./simple_agent_tb.sv");
		
		build_spec.addCCFlag("-I./uvm/src/dpi");
		build_spec.addCCFile("./uvm/src/dpi/uvm_dpi.cc");
		
		SimRunSpec run_spec = new SimRunSpec();
		run_spec.addTopModule("simple_agent_tb");
		run_spec.setTranscriptPath(sim_log.getAbsolutePath());
	
		ISimToolchain toolchain = SimToolchainUtils.getToolchain(sim);
		
		if (toolchain == null) {
			System.out.println("Toolchain null");
		}
		
		if (toolchain == null || !toolchain.is_valid()) {
			System.out.println("Toolchain invalid");
			return;
		}

		toolchain.run(fLog, fTmpDir, build_spec, run_spec);
		
		InputStream in = new FileInputStream(sim_log);
		
		List<String> lines_filt = TestUtils.sed(
				TestUtils.read(in),
				new String[] {"/^# //g"});
		in.close();

		List<String> lines = TestUtils.grep(
				lines_filt,
				new String[] {"ITEM.*"},
				new String[] {});
		
		for (String line : lines) {
			fLog.debug("Final Line: " + line);
		}
		
		assertEquals(10, lines.size());
		
		for (int i=0; i<10; i++) {
			String exp = "ITEM: A=" + i + " B=" + (i+5);
			assertEquals("Line: " + (i+1), exp, lines.get(i));
		}
	}

}
