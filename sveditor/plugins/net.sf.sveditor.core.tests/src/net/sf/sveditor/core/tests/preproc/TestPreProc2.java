package net.sf.sveditor.core.tests.preproc;

import java.io.File;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.preproc.ISVPreProcIncFileProvider;
import net.sf.sveditor.core.preproc.SVPathPreProcIncFileProvider;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor2;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestPreProc2 extends SVCoreTestCaseBase {
	
	public void testBasicInclude() {
		SVCorePlugin.getDefault().enableDebug(false);
		File dir1 = new File(fTmpDir, "dir1");
		File dir2 = new File(fTmpDir, "dir2");
		
		assertTrue(dir1.mkdirs());
		assertTrue(dir2.mkdirs());
		
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		inc_provider.addIncdir(dir1.getAbsolutePath());
		inc_provider.addIncdir(dir2.getAbsolutePath());

		TestUtils.copy(
				"This is file1.svh\n",
				new File(dir1, "file1.svh"));
		
		TestUtils.copy(
				"This is file2.svh\n",
				new File(dir1, "file2.svh"));
		
		runTest(
				"`include \"file1.svh\"\n" +
				"post-file1.svh\n" +
				"`include \"file2.svh\"\n" +
				"post-file2.svh\n",
				inc_provider,
				"This is file1.svh\n" +
				"\n" +
				"post-file1.svh\n" +
				"This is file2.svh\n" +
				"\n" +
				"post-file2.svh\n");
	}
	
	public void testBasicDefine() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		runTest(
				"`define A BB\n" +
				"\n" +
				"`A\n",
				inc_provider,
				"\n" +
				"\n" +
				" BB\n"
				);
	}	

	public void testRecursiveDefine() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		runTest(
				"`define A(a) \\\n" +
				"	`define MACRO_``a 5\n" +
				"\n" +
				"`A(20)\n" +
				"`MACRO_20\n",
				inc_provider,
				"\n" +
				"\n" +
				" \n" +
				"	\n" +
				" 5\n"
				);
	}
	
	public void testDefineFromInclude() {
		SVCorePlugin.getDefault().enableDebug(false);
		File dir1 = new File(fTmpDir, "dir1");
		File dir2 = new File(fTmpDir, "dir2");
		
		assertTrue(dir1.mkdirs());
		assertTrue(dir2.mkdirs());
		
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		inc_provider.addIncdir(dir1.getAbsolutePath());
		inc_provider.addIncdir(dir2.getAbsolutePath());

		TestUtils.copy(
				"`ifndef A\n" +
				"`define A 5\n" +
				"`endif\n",
				new File(dir1, "file1.svh"));
		
		TestUtils.copy(
				"`ifndef A\n" +
				"`define A 6\n" +
				"`endif\n",
				new File(dir1, "file2.svh"));
		
		runTest(
				"`include \"file1.svh\"\n" +
				"`include \"file2.svh\"\n" +
				"`A\n",
				inc_provider,
				"\n" +
				"\n" +
				"\n" +
				"\n" +
				"  \n" +
				"\n" +
				" 5\n");
	}
	
	private void runTest(
			String							doc,
			ISVPreProcIncFileProvider		inc_provider,
			String							exp) {
		
		SVPreProcessor2 preproc = new SVPreProcessor2(
				getName(), new StringInputStream(doc), 
				inc_provider, null);
	
		SVPreProcOutput output = preproc.preprocess();
		
		for (String file : output.getFileList()) {
			fLog.debug("File: " + file);
		}
		
		printFileTree("", output.getFileTree());

		fLog.debug("Output:\n" + output.toString());
		
		assertEquals(exp, output.toString());
	}
	
	private void printFileTree(String ind, SVDBFileTree ft) {
		fLog.debug(ind + "FileTree: " + ft.fFilePath);
		
		for (SVDBFileTree ft_s : ft.fIncludedFileTrees) {
			printFileTree(ind + "  ", ft_s);
		}
	}

}
