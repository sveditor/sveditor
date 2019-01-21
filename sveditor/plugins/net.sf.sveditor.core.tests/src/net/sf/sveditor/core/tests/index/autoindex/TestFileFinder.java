package net.sf.sveditor.core.tests.index.autoindex;

import java.io.File;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.BundleUtils;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.db.index.auto.SVAutoIndexRootfileFinder;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestFileFinder extends SVCoreTestCaseBase {
	
	public void testFindUvmFilesFS() {
		BundleUtils utils = SVCoreTestsPlugin.getBundleUtils();
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
	
		SVAutoIndexRootfileFinder finder = new SVAutoIndexRootfileFinder(
				new SVDBFSFileSystemProvider(),
				SVCorePlugin.getDefault().getFileExtProvider());
		
		SVAutoIndexRootfileFinder.Result result = finder.find(
				new NullProgressMonitor(),
				(new File(fTmpDir, "uvm")).getAbsolutePath());
	
//		System.out.println("Result: " + result.fFilePaths.size());
//		for (String path : result.fFilePaths) {
//			System.out.println("Path: " + path);
//		}
		assertEquals(167, result.fFilePaths.size());
	}
	
	public void testFindUvmFilesWS() {
		BundleUtils utils = SVCoreTestsPlugin.getBundleUtils();
		
		utils.unpackBundleZipToFS("/uvm.zip", fTmpDir);
		
		IProject p = TestUtils.createProject("uvm",
				new File(fTmpDir, "uvm"));
		addProject(p);
	
		SVAutoIndexRootfileFinder finder = new SVAutoIndexRootfileFinder(
				new SVDBWSFileSystemProvider(),
				SVCorePlugin.getDefault().getFileExtProvider());
		
		SVAutoIndexRootfileFinder.Result result = finder.find(
				new NullProgressMonitor(), "${workspace_loc}/uvm");
	
//		System.out.println("Result: " + result.fFilePaths.size());
//		for (String path : result.fFilePaths) {
//			System.out.println("Path: " + path);
//		}
		
		assertEquals(167, result.fFilePaths.size());
	}	
}
