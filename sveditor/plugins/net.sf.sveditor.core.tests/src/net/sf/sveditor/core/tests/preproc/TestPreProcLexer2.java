package net.sf.sveditor.core.tests.preproc;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.parser.SVLexer;
import net.sf.sveditor.core.parser.SVToken;
import net.sf.sveditor.core.preproc.ISVPreProcIncFileProvider;
import net.sf.sveditor.core.preproc.SVPathPreProcIncFileProvider;
import net.sf.sveditor.core.preproc.SVPreProcOutput;
import net.sf.sveditor.core.preproc.SVPreProcessor2;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;

public class TestPreProcLexer2 extends SVCoreTestCaseBase {
	
	public void testBasicInclude() {
		SVCorePlugin.getDefault().enableDebug(true);
		File dir1 = new File(fTmpDir, "dir1");
		File dir2 = new File(fTmpDir, "dir2");
		
		assertTrue(dir1.mkdirs());
		assertTrue(dir2.mkdirs());
		
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		inc_provider.addIncdir(dir1.getAbsolutePath());
		inc_provider.addIncdir(dir2.getAbsolutePath());

		TestUtils.copy(
				"class file1;\n" +
				"\n" +
				"endclass\n",
				new File(dir1, "file1.svh"));
		
		TestUtils.copy(
				"class file2;\n" +
				"\n" +
				"endclass\n",
				new File(dir1, "file2.svh"));
		
		runTest(
				"\n" +
				"\n" +
				"`include \"file1.svh\"\n" +
				"class post_file1;\n" +
				"endclass\n" +
				"`include \"file2.svh\"\n" +
				"class post_file2;\n" +
				"endclass\n",
				inc_provider,
				new String[] {
						"class", "file1", ";",
						"endclass",
						
						"class", "post_file1", ";",
						"endclass",
						
						"class", "file2", ";",
						"endclass",
						
						"class", "post_file2", ";",
						"endclass"
				},
				new SVDBLocation[] {
						
				});
	}

	/*
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
	 */
	
	private void runTest(
			String						doc,
			ISVPreProcIncFileProvider	inc_provider,
			String						images[],
			SVDBLocation				locations[]) {
		
		SVPreProcessor2 preproc = new SVPreProcessor2(
				getName(), new StringInputStream(doc), 
				inc_provider, null);
	
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		SVPreProcOutput output = preproc.preprocess(markers);
		
		List<SVPreProcOutput.FileChangeInfo> file_map = output.getFileMap();
		
		for (SVPreProcOutput.FileChangeInfo e : file_map) {
			fLog.debug("FileMap Entry: " + e.fStartIdx + " " + e.fFileId + " " + e.fLineno);
		}
		
		SVLexer lexer = new SVLexer();
		lexer.init(null, output);

		SVToken t;
		while ((t = lexer.consumeToken()) != null) {
			fLog.debug("Token: " + t.getImage() + " @ " + 
					t.getStartLocation().getFileId() + ":" +
					t.getStartLocation().getLine());
		}
	}
	
	private void printFileTree(String ind, SVDBFileTree ft) {
		fLog.debug(ind + "FileTree: " + ft.fFilePath);
		
		for (SVDBFileTree ft_s : ft.fIncludedFileTrees) {
			printFileTree(ind + "  ", ft_s);
		}
	}

}
