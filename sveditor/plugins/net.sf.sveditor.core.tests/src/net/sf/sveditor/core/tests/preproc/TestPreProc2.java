package net.sf.sveditor.core.tests.preproc;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBLocation;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerKind;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
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
	
	public void testIfdef_1() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		runTest(
				"`define SPI_MAX_CHAR_128\n" +
				"\n" +
				"`ifdef SPI_MAX_CHAR_128\n" +
				"`define SPI_MAX_CHAR 128\n" +
				"`define SPI_CHAR_LEN_BITS 7\n" +
				"`endif\n" +
				"`ifdef SPI_MAX_CHAR_64\n" +
				"`define SPI_MAX_CHAR 64\n" +
				"`define SPI_CHAR_LEN_BITS 6\n" +
				"`endif\n" +
				"`ifdef SPI_MAX_CHAR_32\n" +
				"`define SPI_MAX_CHAR 32\n" +
				"`define SPI_CHAR_LEN_BITS 5\n" +
				"`endif\n" +
				"`SPI_CHAR_LEN_BITS\n",
				inc_provider,
				"\n" +
				"\n" +
				"\n" +
				"\n" +
				"\n" +
				"\n" +
				"   \n" +
				"   \n" +
				" 7\n"
				);
	}

	public void testBitRangeMacroExpansion() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		runTest(
				"`define SPI_CHAR_LEN_BITS     7\n" +
				"wire    [`SPI_CHAR_LEN_BITS:0] tx_bit_pos;\n",
				inc_provider,
				"\n" +
				"wire    [     7:0] tx_bit_pos;\n"
				);
	}

	public void testMissingIncludeWithoutIfdefs() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		runTestExpErrors(
				"/** This is a comment */\n" +
				"`include \"missing.svh\"\n" +
				"/** This is another comment */\n",
				inc_provider,
				new SVDBMarker[] {
						new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
								"Failed to find include file missing.svh",
								new SVDBLocation(0, 2, 0))
				}
				);
	}

	public void testMissingIncludeWithIfdefs() {
		SVCorePlugin.getDefault().enableDebug(false);
		
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		runTestExpErrors(
				"`ifndef INCLUDED_FILE_SVH\n" +
				"`define INCLUDED_FILE_SVH\n" +
				"/** This is a comment */\n" +
				"`include \"missing.svh\"\n" +
				"/** This is another comment */\n" +
				"`endif /* INCLUDED_FILE_SVH */\n",
				inc_provider,
				new SVDBMarker[] {
						new SVDBMarker(MarkerType.Error, MarkerKind.MissingInclude, 
								"Failed to find include file missing.svh",
								new SVDBLocation(0, 4, 0))
				}
				);
	}
	
	public void testMacroExpansionInDisabledRegion() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"class foo extends uvm_component;\n" +
			"\n" +
			"task run_phase(uvm_phase phase);\n" +
			"\n" +
			" `ifdef UNDEFINED // MSB      \n" +
			"\n" +
			" uvm_report_warning( \"BAR\", s,, `__FILE__,`__LINE__);\n" +
			"\n" +
			" `endif // MSB      	\n" +
			" endtask\n" +
			"endclass\n"
			;
		String exp =
			"class foo extends uvm_component;\n" +
			"\n" +
			"task run_phase(uvm_phase phase);\n" +
			"\n" +
			"       \n" +
			" endtask\n" +
			"endclass\n"
			;
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		runTest(
				doc,
				inc_provider,
				exp
				);
	}
	
	public void testMacroInString() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"`define macro foo\n" +
			"`define msg(ID, MSG) report(ID, MSG)\n" +
			"`msg(\"id\", \"don't expand `macro\");\n"
			;
		String exp =
			"\n" +
			"\n" +
			" report(\"id\", \"don't expand `macro\");\n"
			;
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		runTest(
				doc,
				inc_provider,
				exp
				);		
	}

	public void testCommentInMacroCall() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"`define macro foo\n" +
			"`define msg(ID, MSG, VERB) report(ID, MSG, VERB)\n" +
			"`msg(\"id\",\n" +
			"	/* block comment */\n" +
			"	\"does not\",\n" +
			"	// \"previous comment\",\n" +
			"	VERBOSITY);\n"
			;
		String exp =
			"\n" +
			"\n" +
			" report(\"id\", \"does not\", VERBOSITY);\n"
			;
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		runTest(
				doc,
				inc_provider,
				exp
				);		
	}

	public void testMacroExternFunctionClassname() {
		SVCorePlugin.getDefault().enableDebug(true);
		String doc =
			"`define CLS myclass\n" +
			"function `CLS::myfunction;\n" +
			"endfunction\n"
			;
		String exp =
			"\n" +
			"function  myclass::myfunction;\n" +
			"endfunction\n"
			;
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		runTest(
				doc,
				inc_provider,
				exp
				);		
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

		fLog.debug("==");
		fLog.debug("Output:\n" + output.toString());
		fLog.debug("==");
		fLog.debug("Exp:\n" + exp);
		fLog.debug("==");
		
		assertEquals(exp, output.toString());
	}

	private void runTestExpErrors(
			String							doc,
			ISVPreProcIncFileProvider		inc_provider,
			SVDBMarker						errors[]) {
		List<SVDBMarker> unmatched = new ArrayList<SVDBMarker>();
		
		for (SVDBMarker m : errors) {
			unmatched.add(m);
		}
		
		SVPreProcessor2 preproc = new SVPreProcessor2(
				getName(), new StringInputStream(doc), 
				inc_provider, null);
	
		SVPreProcOutput output = preproc.preprocess();
		
		for (String file : output.getFileList()) {
			fLog.debug("File: " + file);
		}
		
		printFileTree("", output.getFileTree());

		fLog.debug("Output:\n" + output.toString());
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		collectMarkers(markers, preproc.getFileTree());
	
		for (int i=0; i<markers.size(); i++) {
			SVDBMarker m = markers.get(i);
			
			fLog.debug("Marker: " + m.getMessage() + ":" + m.getMarkerType() + ":" + m.getKind() + ":" + 
					m.getLocation().getFileId() + ":" + m.getLocation().getLine() + ":" +
					m.getLocation().getPos());
			
			if (unmatched.contains(m)) {
				markers.remove(i);
				i--;
				unmatched.remove(m);
			}
		}
		
		StringBuilder sb = new StringBuilder();
		
		for (SVDBMarker m : unmatched) {
			fLog.debug("Failed to match marker: " + m.getMessage() + ":" + m.getMarkerType() + ":" + m.getKind() + ":" + 
					m.getLocation().getFileId() + ":" + m.getLocation().getLine() + ":" +
					m.getLocation().getPos());
			sb.append("m=" + m.getMessage() + ":" + m.getMarkerType() + ":" + m.getKind() + ":" + 
					m.getLocation().getFileId() + ":" + m.getLocation().getLine() + ":" +
					m.getLocation().getPos() + " ; ");
		}
		
		assertEquals("Failed to find markers: " + sb.toString(), 0, unmatched.size());
	
		sb.setLength(0);
		for (SVDBMarker m : unmatched) {
			fLog.debug("Unexpected marker: " + m.getMessage() + ":" + m.getMarkerType() + ":" + m.getKind() + ":" + 
					m.getLocation().getFileId() + ":" + m.getLocation().getLine() + ":" +
					m.getLocation().getPos());
			sb.append("m=" + m.getMessage() + ":" + m.getMarkerType() + ":" + m.getKind() + ":" + 
					m.getLocation().getFileId() + ":" + m.getLocation().getLine() + ":" +
					m.getLocation().getPos() + " ; ");
		}
		
		assertEquals("Unexpected markers: " + sb.toString(), 0, unmatched.size());
	}
	
	private void collectMarkers(List<SVDBMarker> markers, SVDBFileTree ft) {
		markers.addAll(ft.getMarkers());
		
		for (SVDBFileTree ft_i : ft.getIncludedFileTreeList()) {
			collectMarkers(markers, ft_i);
		}
	}
	
	private void printFileTree(String ind, SVDBFileTree ft) {
		fLog.debug(ind + "FileTree: " + ft.fFilePath);
		
		for (SVDBFileTree ft_s : ft.fIncludedFileTrees) {
			printFileTree(ind + "  ", ft_s);
		}
	}

}
