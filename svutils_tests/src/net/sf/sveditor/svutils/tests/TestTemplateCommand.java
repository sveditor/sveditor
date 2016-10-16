package net.sf.sveditor.svutils.tests;

import java.io.File;

import net.sf.sveditor.svutils.SVUtils;

public class TestTemplateCommand extends SVUtilsTestBase {
	
	public void testRunTemplateCommand() {
		SVUtils utils = new SVUtils();
		copyResourceDir("/data/sve_templates", fTmpDir);
		
		utils.run(new String[] {
				"template",
				"list",
				"-tp",
				(new File(fTmpDir, "sve_templates")).getAbsolutePath()
		});
		
	}

}
