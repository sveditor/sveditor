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
	
	public void testMultiLineStringMacro() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
				"`define uvm_error(t, str) \\\n" +
				"string type = t;\\\n" +
				"string msg = str;\\\n" +
				"\n" +
				"`uvm_error(\"foo\", \"More than 256 items have accumulated in the \\\n" +
				"transaction layer, and a sequence continues to send items\")\n" 
				;
		String exp = 
				"string type = \"foo\";\n" +
				"string msg = \"More than 256 items have accumulated in the transaction layer, and a sequence continues to send items\";";
		SVPathPreProcIncFileProvider inc_provider =
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
		
		
		runTestTrim(content, inc_provider, exp);
	}
	
	public void testUvmRecordFieldExpansion() {
		SVCorePlugin.getDefault().enableDebug(false);
		String content = 
			"`define UVM_USE_P_FORMAT\n" +
			"`define uvm_record_field(NAME,VALUE) \\\n" +
			"	if (recorder != null && recorder.tr_handle != 0) begin \\\n" +
			"		if (recorder.get_type_name() != \"uvm_recorder\") begin \\\n" +
			"			`uvm_record_attribute(recorder.tr_handle,NAME,VALUE) \\\n" +
			"		end \\\n" +
			"	else \\\n" +
			"		`ifdef UVM_USE_P_FORMAT \\\n" +
			"		recorder.m_set_attribute(recorder.tr_handle,NAME,$sformatf(\"%p\",VALUE)); \\\n" +
			"		`else \\\n" +
			"		recorder.m_set_attribute(recorder.tr_handle,NAME,`\"value of VALUE`\"); \\\n" +
			"		`endif \\\n" +
			"	end\n" +
			"\n" +
			"`uvm_record_field(\"address\",m_address)\n" +
			"\n"
			;
		String exp = 
				"if (recorder != null && recorder.tr_handle != 0) begin \n" +
				"		if (recorder.get_type_name() != \"uvm_recorder\") begin \n" +
				"			`undefined \n" +
				"		end \n" +
				"	else \n" +
				"		 \n" +
				"		recorder.m_set_attribute(recorder.tr_handle,\"address\",$sformatf(\"%p\",m_address)); \n" +
				"		 \n" +
				"	end";
		
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
		
		runTestTrim2(content, inc_provider, exp);
	}
	
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

	public void testMacroInclude() {
		SVCorePlugin.getDefault().enableDebug(false);
		File dir1 = new File(fTmpDir, "dir1");
		
		assertTrue(dir1.mkdirs());
		
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		inc_provider.addIncdir(dir1.getAbsolutePath());

		TestUtils.copy(
				"class classb;\n" +
				"endclass\n",
				new File(dir1, "classb.svh"));
		
		runTest(
				"`define CLASSB_SV \"classb.svh\"\n" +
				"`include `CLASSB_SV\n" +
				"class top_class; \n" +
				"endclass\n",
				inc_provider,
				""
				);
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
								SVDBLocation.pack(0,  2,  0))
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
								SVDBLocation.pack(0, 4, 0))
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
		SVCorePlugin.getDefault().enableDebug(false);
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

	public void testIfndefElse() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"`define VMM_SCENARIO foo_scenario\n" +
			"`ifndef MACRO_DEFINED\n" +
			"task vmm_channel::put(vmm_data obj,\n" +
			"					int offset=-1,\n" +
			"					`VMM_SCENARIO grabber=null);\n" +
			"`else\n" +
			"task vmm_channel::put(vmm_data obj,\n" +
			"					int offset=-1);\n" +
			"`endif\n" +
			"section_3\n"
			;
		String exp =
			"\n" +
			"\n" +
			"task vmm_channel::put(vmm_data obj,\n" +
			"					int offset=-1,\n" +
			"					 foo_scenario grabber=null);\n" +
			" \n" +
			"section_3\n"
			;
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		runTest(
				doc,
				inc_provider,
				exp
				);		
	}

	/*
	public void testIfdefFILE() {
		SVCorePlugin.getDefault().enableDebug(false);
		String doc =
			"`define VMM_LOG_FORMAT_FILE_LINE\n" +
			"      `ifdef VMM_LOG_FORMAT_FILE_LINE\n" +
			"			if (this.start_msg(FAILURE_TYP, WARNING_SEV, `__FILE__, `__LINE__)) begin\n" +
			"      `else\n" +
			"			if (this.start_msg(FAILURE_TYP, WARNING_SEV)) begin\n" +
			"      `endif\n" +
			""
			;
		String exp =
			"\n" +
			"\n" +
			"task vmm_channel::put(vmm_data obj,\n" +
			"					int offset=-1,\n" +
			"					 foo_scenario grabber=null);\n" +
			" \n" +
			"section_3\n"
			;
		SVPathPreProcIncFileProvider inc_provider = 
				new SVPathPreProcIncFileProvider(new SVDBFSFileSystemProvider());
			
		runTest(
				doc,
				inc_provider,
				exp
				);		
	}
	 */
	
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
		
//		String out = output.toString().trim();
		String out = output.toString();

		fLog.debug("==");
		fLog.debug("Output:\n" + out);
		fLog.debug("==");
		fLog.debug("Exp:\n" + exp);
		fLog.debug("==");
		
		assertEquals(exp, out);
	}

	private void runTestTrim(
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
		
		String out = output.toString().trim();

		fLog.debug("==");
		fLog.debug("Output:\n" + out);
		fLog.debug("==");
		fLog.debug("Exp:\n" + exp);
		fLog.debug("==");
		
		assertEquals(exp, out);
	}

	private void runTestTrim2(
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
		
		String out = trimLines(output.toString());
		exp = trimLines(exp);
		
		fLog.debug("==");
		fLog.debug("Output:\n" + out);
		fLog.debug("==");
		fLog.debug("Exp:\n" + exp);
		fLog.debug("==");
		
		assertEquals(exp, out);
	}
	
	public static String trimLines(String in) {
		StringBuilder ret = new StringBuilder();
		int idx=0, start=0;
		
		while (idx < in.length()) {
			if (in.charAt(idx) == '\n') {
				String line = in.substring(start, idx).trim();
				if (!line.equals("")) {
					ret.append(line);
					ret.append('\n');
				}
				start = idx+1;
			}
			idx++;
		}
		if (start < idx) {
			// Add the last line
			String line = in.substring(start).trim();
			if (!line.equals("")) {
				ret.append(line);
				ret.append('\n');
			}
		}
		
		return ret.toString();
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
					SVDBLocation.unpackFileId(m.getLocation()) + ":" + 
					SVDBLocation.unpackLineno(m.getLocation()) + ":" +
					SVDBLocation.unpackPos(m.getLocation()));
			
			if (unmatched.contains(m)) {
				markers.remove(i);
				i--;
				unmatched.remove(m);
			}
		}
		
		StringBuilder sb = new StringBuilder();
		
		for (SVDBMarker m : unmatched) {
			fLog.debug("Failed to match marker: " + m.getMessage() + ":" + m.getMarkerType() + ":" + m.getKind() + ":" + 
					SVDBLocation.unpackFileId(m.getLocation()) + ":" + 
					SVDBLocation.unpackLineno(m.getLocation()) + ":" +
					SVDBLocation.unpackPos(m.getLocation()));
			sb.append("m=" + m.getMessage() + ":" + m.getMarkerType() + ":" + m.getKind() + ":" + 
					SVDBLocation.unpackFileId(m.getLocation()) + ":" + 
					SVDBLocation.unpackLineno(m.getLocation()) + ":" +
					SVDBLocation.unpackPos(m.getLocation()) + " ; ");
		}
		
		assertEquals("Failed to find markers: " + sb.toString(), 0, unmatched.size());
	
		sb.setLength(0);
		for (SVDBMarker m : unmatched) {
			fLog.debug("Unexpected marker: " + m.getMessage() + ":" + m.getMarkerType() + ":" + m.getKind() + ":" + 
					SVDBLocation.unpackFileId(m.getLocation()) + ":" + 
					SVDBLocation.unpackLineno(m.getLocation()) + ":" +
					SVDBLocation.unpackPos(m.getLocation()));
			sb.append("m=" + m.getMessage() + ":" + m.getMarkerType() + ":" + m.getKind() + ":" + 
					SVDBLocation.unpackFileId(m.getLocation()) + ":" + 
					SVDBLocation.unpackLineno(m.getLocation()) + ":" +
					SVDBLocation.unpackPos(m.getLocation()) + " ; ");
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
