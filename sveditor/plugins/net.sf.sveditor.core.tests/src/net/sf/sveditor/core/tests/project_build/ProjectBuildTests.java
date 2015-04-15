package net.sf.sveditor.core.tests.project_build;

import junit.framework.TestSuite;

public class ProjectBuildTests extends TestSuite {
	
	public ProjectBuildTests() {
		addTest(new TestSuite(TestProjectBuildUBus.class));
		
	}
	
	public static TestSuite suite() {
		return new ProjectBuildTests();
	}

}
