package net.sf.sveditor.core.tests.index;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBThreadedArgFileIndex;
import net.sf.sveditor.core.db.index.SVDBThreadedSourceCollectionIndex;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.db.index.cache.InMemoryIndexCache;
import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;
import net.sf.sveditor.core.fileset.SVFileSet;
import net.sf.sveditor.core.fileset.SVWorkspaceFileMatcher;
import net.sf.sveditor.core.tests.SVCoreTestsPlugin;
import net.sf.sveditor.core.tests.TestIndexCacheFactory;
import net.sf.sveditor.core.tests.utils.BundleUtils;
import net.sf.sveditor.core.tests.utils.TestUtils;

import junit.framework.TestCase;

public class TestThreadedSourceCollectionIndex extends TestCase {
	private File			fTmpDir;
	private IProject		fProject;

	@Override
	protected void setUp() throws Exception {
		fTmpDir = TestUtils.createTempDir();
	}

	@Override
	protected void tearDown() throws Exception {
		if (fProject != null) {
//			TestUtils.deleteProject(fProject);
		}
	}

	public void testParseUVM() {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		SVDBWSFileSystemProvider fs_provider = new SVDBWSFileSystemProvider();
		
		File project = new File(fTmpDir, "project");
		project.mkdirs();
		utils.unpackBundleZipToFS("/uvm.zip", project);
		
		fProject = TestUtils.createProject("project", project);
		String base = "/project/uvm/src";
		List<AbstractSVFileMatcher> matcher_list = new ArrayList<AbstractSVFileMatcher>();
		SVWorkspaceFileMatcher matcher = new SVWorkspaceFileMatcher();
		SVFileSet fs = new SVFileSet(base);
//		fs.addInclude(SVCorePlugin.getDefault().getDefaultSourceCollectionIncludes());
//		fs.addExclude(SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes());
		fs.addInclude("**/*.sv");
		fs.addInclude("**/*.svh");
//		fs.addExclude(SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes());
		
		matcher_list.add(matcher);
		matcher.addFileSet(fs);
		
		SVDBThreadedSourceCollectionIndex index = new SVDBThreadedSourceCollectionIndex(
				"project", "${workspace_loc}/project",
				matcher_list, 
				fs_provider, 
				new InMemoryIndexCache(), 
				null);
		index.init(new NullProgressMonitor());
		
		long start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long end = System.currentTimeMillis();
		
		System.out.println("Total time: " + (end-start));
	}

	public void testParseUVMArgFile() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
		SVDBWSFileSystemProvider fs_provider = new SVDBWSFileSystemProvider();
		
		File project = new File(fTmpDir, "project");
		project.mkdirs();
		utils.unpackBundleZipToFS("/uvm.zip", project);
		
		fProject = TestUtils.createProject("project", project);

		PrintStream ps = new PrintStream(new File(project, "files.f"));
		ps.println("+incdir+./uvm/src");
		ps.println("uvm/src/uvm_pkg.sv");
		
		SVDBThreadedArgFileIndex index = new SVDBThreadedArgFileIndex(
				"project", 
				"${workspace_loc}/project/files.f",
				fs_provider,
				new InMemoryIndexCache(), 
				null);
		index.init(new NullProgressMonitor());
		
		long start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		long end = System.currentTimeMillis();
		
		System.out.println("Total time: " + (end-start));
	}

	public void testParseOpenSparcArgFile() throws IOException {
		SVCorePlugin.getDefault().enableDebug(false);
		BundleUtils utils = new BundleUtils(SVCoreTestsPlugin.getDefault().getBundle());
		
//		SVDBWSFileSystemProvider fs_provider = new SVDBWSFileSystemProvider();
		SVDBFSFileSystemProvider fs_provider = new SVDBFSFileSystemProvider();
		
		TestIndexCacheFactory cf = new TestIndexCacheFactory(fTmpDir);
		
		SVDBThreadedArgFileIndex index = new SVDBThreadedArgFileIndex(
				"project", 
				"/home/ballance.1/Downloads/OpenSPARCT2/design/design.f",
				fs_provider,
				cf.createIndexCache("project", "/home/ballance.1/Downloads/OpenSPARCT2/design/design.f"), 
				null);
		index.init(new NullProgressMonitor());
		
		long start = System.currentTimeMillis();
		index.loadIndex(new NullProgressMonitor());
		index.dispose();
		long end = System.currentTimeMillis();

		System.out.println("Total time: " + (end-start));
	}

}
