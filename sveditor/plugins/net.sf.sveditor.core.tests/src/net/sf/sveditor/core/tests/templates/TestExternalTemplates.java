package net.sf.sveditor.core.tests.templates;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.templates.IExternalTemplatePathProvider;
import net.sf.sveditor.core.templates.TemplateInfo;
import net.sf.sveditor.core.templates.TemplateRegistry;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import junit.framework.TestCase;

public class TestExternalTemplates extends TestCase {
	
	private File			fTmp;
	
	@Override
	protected void setUp() throws Exception {
		fTmp = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		TestUtils.delete(fTmp);
	}

	public void testDiscoverTemplatesFS() throws IOException {
		String testname = "testDiscoverTemplatesFS";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(true);
		final File tmpl_dir = new File(fTmp, "templates");
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.copyBundleDirToFS("/templates/collection1", tmpl_dir);
		
		TemplateRegistry rgy = new TemplateRegistry(new IExternalTemplatePathProvider() {
			
			public List<String> getExternalTemplatePath() {
				List<String> ret = new ArrayList<String>();
				ret.add(tmpl_dir.getAbsolutePath());
				return ret;
			}
		}, false);
		
		List<String> categories = rgy.getCategoryIDs();
		for (String category : categories) {
			log.debug("Category: " + category);
		}
		
		TestUtils.assertContains(categories, "default");
		LogFactory.removeLogHandle(log);
		
		List<TemplateInfo> ti_l = rgy.getTemplates("default");
		List<String> templates = new ArrayList<String>();
		
		for (TemplateInfo t : ti_l) {
			log.debug("Template ID: " + t.getId());
			templates.add(t.getId());
		}
		
		TestUtils.assertContains(templates, 
				"collection1.t1", "collection1.t1_1",
				"collection1.t2.t2_1", "collection1.t2.t2_2");
		
		TemplateInfo ti = rgy.findTemplate("collection1.t1");
		assertNotNull(ti);
		
		Iterable<Tuple<String, String>> tf_it = ti.getTemplates();
		List<String> tfn_list = new ArrayList<String>();
		
		for (Tuple<String, String> tf : tf_it) {
			File file = new File(tf.first());
			log.debug("Template File: " + file.getName());
			tfn_list.add(file.getName());
		}
		
		// Ensure that the finder located the implicitly-specified files
		TestUtils.assertContains(tfn_list, "t1.svh", "t1.f");
		
		// Ensure that all template files exist
		for (String category : rgy.getCategoryIDs()) {
			for (TemplateInfo t : rgy.getTemplates(category)) {
				for (Tuple<String, String> tf : t.getTemplates()) {
					File file = new File(tf.first());
					assertTrue("File " + tf.first() + " does not exist", file.isFile());
				}
			}
		}
	}
}
