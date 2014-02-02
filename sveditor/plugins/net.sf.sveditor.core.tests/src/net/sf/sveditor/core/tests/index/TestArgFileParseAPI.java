package net.sf.sveditor.core.tests.index;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.project.SVDBProjectData;
import net.sf.sveditor.core.db.project.SVDBProjectManager;
import net.sf.sveditor.core.db.project.SVProjectFileWrapper;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestArgFileParseAPI extends SVCoreTestCaseBase {
	
	public void testMissingIncludeResolved() throws CoreException {
		SVCorePlugin.getDefault().enableDebug(false);
		

		File pdir = new File(fTmpDir, "missing_inc");
		assertTrue(pdir.mkdirs());
		
		IProject p = TestUtils.createProject("missing_inc", pdir);
		addProject(p);
	
		IFolder incdir = p.getFolder("incdir");
		incdir.create(true, true, new NullProgressMonitor());
	
		TestUtils.copy(
				"class foobar;\n" +
				"endclass\n",
				incdir.getFile("foobar.svh"));
	
		String my_class1_svh = 
				"`include \"foobar.svh\"\n" +
				"class my_class1;\n" +
				"endclass\n";
		
		TestUtils.copy(my_class1_svh,
				p.getFile("my_class1.svh"));
		
		TestUtils.copy(
				"my_class1.svh",
				p.getFile("missing_inc.f"));
		
		// Setup the project
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVDBProjectManager pmgr = SVCorePlugin.getDefault().getProjMgr();
		
		SVDBProjectData pdata = pmgr.getProjectData(p);
		
		SVProjectFileWrapper fw = pdata.getProjectFileWrapper();
		
		fw.addArgFilePath("${project_loc}/missing_inc.f");
		
		pdata.setProjectFileWrapper(fw, true);
		
		// Build the project
		pmgr.rebuildProject(new NullProgressMonitor(), p);
		
		pdata.getProjectIndexMgr().parse(new NullProgressMonitor(), 
				new StringInputStream(my_class1_svh), 
				"${workspace_loc}/missing_inc/my_class1.svh", 
				markers);
		
		assertEquals(1, markers.size());
		
		// Now, add the missing include path
		TestUtils.copy(
				"+incdir+incdir\n" +
				"my_class1.svh",
				p.getFile("missing_inc.f"));		
		
		// Re-build the project
		pmgr.rebuildProject(new NullProgressMonitor(), p);
	
		// Re-parse the file
		markers.clear();
		pdata.getProjectIndexMgr().parse(new NullProgressMonitor(), 
				new StringInputStream(my_class1_svh), 
				"${workspace_loc}/missing_inc/my_class1.svh", 
				markers);
	
		// Confirm that the missing include is found now
		assertEquals(0, markers.size());
	}

}
