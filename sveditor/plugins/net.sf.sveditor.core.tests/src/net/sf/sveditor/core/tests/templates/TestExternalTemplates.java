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
import net.sf.sveditor.core.templates.TemplateFSFileCreator;
import net.sf.sveditor.core.templates.TemplateInfo;
import net.sf.sveditor.core.templates.TemplateParameter;
import net.sf.sveditor.core.templates.TemplateParameterProvider;
import net.sf.sveditor.core.templates.TemplateProcessor;
import net.sf.sveditor.core.templates.TemplateRegistry;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;
import net.sf.sveditor.core.text.TagProcessor;

import junit.framework.TestCase;

public class TestExternalTemplates extends TestCase {
	
	private File			fTmpDir;
	
	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		TestUtils.delete(fTmpDir);
	}

	public void testDiscoverTemplatesFS() throws IOException {
		String testname = "testDiscoverTemplatesFS";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		final File tmpl_dir = new File(fTmpDir, "templates");
		
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.copyBundleDirToFS("/templates/collection1", tmpl_dir);
		
		TemplateRegistry rgy = new TemplateRegistry(false);
		rgy.addPathProvider(new IExternalTemplatePathProvider() {
			
			public List<String> getExternalTemplatePath() {
				List<String> ret = new ArrayList<String>();
				ret.add(tmpl_dir.getAbsolutePath());
				return ret;
			}
		});
		rgy.load_extensions();
		
		List<String> categories = rgy.getCategoryIDs();
		for (String category : categories) {
			log.debug("Category: " + category);
		}
		
		TestUtils.assertContains(categories, "default");
		LogFactory.removeLogHandle(log);

		TemplateInfo t1_1 = null;
		
		List<TemplateInfo> ti_l = rgy.getTemplates("default");
		List<String> templates = new ArrayList<String>();
		
		for (TemplateInfo t : ti_l) {
			log.debug("Template ID: " + t.getId());
			templates.add(t.getId());
			if (t.getId().equals("collection1.t1_1")) {
				t1_1 = t;
			}
		}
		
		assertNotNull(t1_1);
		
		List<String> param_names = new ArrayList<String>();
		for (TemplateParameter p : t1_1.getParameters()) {
			param_names.add(p.getName());
		}
		
		TestUtils.assertContains(param_names, "foo1", "foo2");
		
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
	
	public void testSubdirHierarchy() {
		String testname = "testSubdirHierarchy";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.copyBundleDirToFS("/data/templates/subdir_output", fTmpDir);
		
		TemplateRegistry rgy = new TemplateRegistry(false);
		rgy.addPathProvider(new IExternalTemplatePathProvider() {
			public List<String> getExternalTemplatePath() {
				List<String> ret = new ArrayList<String>();
				ret.add(new File(fTmpDir, "subdir_output").getAbsolutePath());
				return ret;
			}
		});
		rgy.load_extensions();
		
		TemplateInfo tmpl = rgy.findTemplate("subdir_output");
		assertNotNull(tmpl);
		
		TagProcessor proc = new TagProcessor();
		TemplateParameterProvider p = new TemplateParameterProvider();
		p.setTag("name", "test");
		proc.addParameterProvider(p);
		
		List<String> files = TemplateProcessor.getOutputFiles(tmpl, proc);
		
		assertContainsAll(files,
				"subdir/test_1.svh",
				"subdir/test_2.svh");
		
		TemplateFSFileCreator out_sp = new TemplateFSFileCreator(fTmpDir);
		TemplateProcessor tp = new TemplateProcessor(out_sp);
		
		tp.process(tmpl, proc);
		
		assertFilesExist(fTmpDir, 
				"subdir/test_1.svh",
				"subdir/test_2.svh");

		LogFactory.removeLogHandle(log);
	}
	
	public void testSpaceContainingFilenames() {
		String testname = "testSpaceContainingFilenames";
		LogHandle log = LogFactory.getLogHandle(testname);
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		utils.copyBundleDirToFS("/data/templates/space_containing_filenames", fTmpDir);
		
		TemplateRegistry rgy = new TemplateRegistry(false);
		rgy.addPathProvider(new IExternalTemplatePathProvider() {
			public List<String> getExternalTemplatePath() {
				List<String> ret = new ArrayList<String>();
				ret.add(new File(fTmpDir, "space_containing_filenames").getAbsolutePath());
				return ret;
			}
		});
		rgy.load_extensions();
		
		TemplateInfo tmpl = rgy.findTemplate("subdir_output");
		assertNotNull(tmpl);
		
		TagProcessor proc = new TagProcessor();
		TemplateParameterProvider p = new TemplateParameterProvider();
		p.setTag("name", "test");
		proc.addParameterProvider(p);
		
		List<String> files = TemplateProcessor.getOutputFiles(tmpl, proc);
		
		assertContainsAll(files,
				"subdir/test_1.svh",
				"subdir/test_2.svh");
		
		TemplateFSFileCreator out_sp = new TemplateFSFileCreator(fTmpDir);
		TemplateProcessor tp = new TemplateProcessor(out_sp);
		
		tp.process(tmpl, proc);
		
		assertFilesExist(fTmpDir, 
				"subdir/test_1.svh",
				"subdir/test_2.svh");

		LogFactory.removeLogHandle(log);
	}
	
	private static void assertFilesExist(File dir, String ... paths) {
		for (String path : paths) {
			File t = new File(dir, path);
			TestCase.assertTrue(
					"File " + t.getPath() + " does not exist",
					t.isFile());
		}
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
