/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.tests.templates;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.tagproc.TagProcessor;
import net.sf.sveditor.core.tagproc.TemplateParameterProvider;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.svt.core.templates.ExtensionPointTemplateRegistry;
import net.sf.sveditor.svt.core.templates.TemplateFSFileCreator;
import net.sf.sveditor.svt.core.templates.TemplateInfo;
import net.sf.sveditor.svt.core.templates.TemplateProcessor;
import net.sf.sveditor.svt.core.templates.WorkspaceTemplateRegistry;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestMethodologyTemplates extends SVCoreTestCaseBase {
	
	public void testUvmAgent() {
		LogHandle log = LogFactory.getLogHandle("testUvmAgent");
		SVCorePlugin.getDefault().enableDebug(false);
		WorkspaceTemplateRegistry rgy = new ExtensionPointTemplateRegistry();
		TemplateInfo tmpl = rgy.findTemplate("org.uvmworld.uvm.uvm_agent");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		assertNotNull(tmpl);
		TagProcessor proc = new TagProcessor();
		TemplateParameterProvider p = new TemplateParameterProvider();
		p.setTag("name", "test");
		proc.addParameterProvider(p);
		
		List<String> files = TemplateProcessor.getOutputFiles(tmpl, proc);
		
		assertContainsAll(files,
				"test_agent_pkg.sv",
				"test_config.svh",
				"test_driver.svh",
				"test_monitor.svh",
				"test_seq_base.svh",
				"test_seq_item.svh",
				"test_agent.svh");
		
		TemplateFSFileCreator out_sp = new TemplateFSFileCreator(fTmpDir);
		TemplateProcessor tp = new TemplateProcessor(out_sp);
		
		tp.process(tmpl, proc);

		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);		

		try {
			PrintStream ps = new PrintStream(new File(fTmpDir, "test_agent_pkg.f"));
			ps.println("+define+QUESTA");
			ps.println("+incdir+./uvm/src");
			ps.println("./uvm/src/uvm_pkg.sv");
			ps.close();
		} catch (IOException e) {
			fail("Problem creating test_agent_pkg.f: " + e.getMessage());
		}

		ISVDBIndex index = fIndexRgy.findCreateIndex(new NullProgressMonitor(), 
				"GLOBAL", new File(fTmpDir, "test_agent_pkg.f").getAbsolutePath(),
				SVDBArgFileIndexFactory.TYPE, null);
		
		IndexTestUtils.assertNoErrWarn(log, index);
		
		LogFactory.removeLogHandle(log);
	}

	private static void assertContainsAll(List<String> target, String ... expected) {
		
		assertEquals(expected.length, target.size());
		
		for (String exp : expected) {
			if (!target.contains(exp)) {
				fail("target does not contain \"" + exp + "\"");
			}
		}
	}
}
