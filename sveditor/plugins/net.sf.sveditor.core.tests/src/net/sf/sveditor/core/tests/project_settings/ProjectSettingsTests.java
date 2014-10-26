package net.sf.sveditor.core.tests.project_settings;

import junit.framework.TestSuite;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;

public class ProjectSettingsTests extends SVCoreTestCaseBase {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("ProjectSettingsTests");
		s.addTest(new TestSuite(TestProjectSettingsVarRefs.class));
		s.addTest(new TestSuite(TestProjectSettingChanges.class));
		return s;
	}
	
}
