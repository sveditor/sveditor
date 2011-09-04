/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
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

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.SVDBIndexRegistry;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.templates.TemplateFSOutStreamProvider;
import net.sf.sveditor.core.templates.TemplateInfo;
import net.sf.sveditor.core.templates.TemplateProcessor;
import net.sf.sveditor.core.templates.TemplateRegistry;
import net.sf.sveditor.core.tests.IndexTestUtils;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestNullIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;
import net.sf.sveditor.core.text.TagProcessor;

import org.eclipse.core.runtime.NullProgressMonitor;

public class TestMethodologyTemplates extends TestCase {
	
	private File				fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
//		TestUtils.delete(fTmpDir);
	}

	public void testUvmAgent() {
		LogHandle log = LogFactory.getLogHandle("testUvmAgent");
		SVCorePlugin.getDefault().enableDebug(false);
		TemplateRegistry rgy = TemplateRegistry.getDefault();
		TemplateInfo tmpl = rgy.findTemplate("org.uvmworld.uvm.uvm_agent");
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		assertNotNull(tmpl);
		TagProcessor proc = new TagProcessor();
		proc.setTag("name", "test");
		
		List<String> files = TemplateProcessor.getOutputFiles(tmpl, proc);
		
		assertContainsAll(files,
				"test_agent_pkg.sv",
				"test_config.svh",
				"test_driver.svh",
				"test_monitor.svh",
				"test_seq_base.svh",
				"test_seq_item.svh",
				"test_agent.svh");
		
		TemplateFSOutStreamProvider out_sp = new TemplateFSOutStreamProvider(fTmpDir);
		TemplateProcessor tp = new TemplateProcessor(out_sp);
		
		tp.process(tmpl, proc);

		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);		

		SVDBIndexRegistry i_rgy = SVCorePlugin.getDefault().getSVDBIndexRegistry();
		i_rgy.init(new TestNullIndexCacheFactory());
		
		try {
			PrintStream ps = new PrintStream(new File(fTmpDir, "test_agent_pkg.f"));
			ps.println("+incdir+./uvm/src");
			ps.println("./uvm/src/uvm_pkg.sv");
			ps.close();
		} catch (IOException e) {
			fail("Problem creating test_agent_pkg.f: " + e.getMessage());
		}
		
		ISVDBIndex index = i_rgy.findCreateIndex(new NullProgressMonitor(), 
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
