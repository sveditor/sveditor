package net.sf.sveditor.ui.tests.console;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.debug.ui.console.FileLink;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.ui.console.IConsoleDocumentPartitioner;
import org.eclipse.ui.console.IHyperlink;
import org.eclipse.ui.console.TextConsole;

import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.script.launch.ILogMessageScanner;
import net.sf.sveditor.core.script.launch.ILogMessageScannerMgr;
import net.sf.sveditor.core.script.launch.ScriptMessage;
import net.sf.sveditor.core.tests.SVCoreTestCaseBase;
import net.sf.sveditor.core.tests.utils.TestUtils;
import net.sf.sveditor.ui.script.launch.GenericPathPatternMatcher;
import net.sf.sveditor.ui.script.launch.GenericRelPathPatternMatcher;

public class TestPathPatternMatcher extends SVCoreTestCaseBase {

	private static class HyperInfo {
		public IHyperlink			fHyperlink;
		public int					fOffset;
		public int					fLength;
		
		public HyperInfo(IHyperlink h, int o, int l) {
			fHyperlink = h;
			fOffset = o;
			fLength = l;
		}
	}
	
	private static class FileInfo {
		public String				fPath;
		public int					fLineno;
		
		public FileInfo(String path, int lineno) {
			fPath = path;
			fLineno = lineno;
		}
	}
	private static class TestTextConsole extends TextConsole {
		
		public TestTextConsole() {
			super("TestTextConsole", "Test", null, false);
		}

		@Override
		protected IConsoleDocumentPartitioner getPartitioner() {
			// TODO Auto-generated method stub
			return null;
		}
		
		@Override
		public void addHyperlink(IHyperlink hyperlink, int offset, int length) throws BadLocationException {
		}
	}
	
	private static class TestGenericPathPathMatcher extends GenericPathPatternMatcher {
		private LogHandle			fLog = LogFactory.getLogHandle("TestGenericPathPathMatcher");
		public List<FileInfo> 		fFileInfo = new ArrayList<FileInfo>();

		@Override
		protected void addIFileLink(IFile file, int lineno, int offset, int length) {
			fLog.debug("addIFileLink: " + file);
			// TODO Auto-generated method stub
//			super.addIFileLink(file, lineno, offset, length);
		}

		@Override
		protected void addFSFileLink(File file, int lineno, int offset, int length) {
			fLog.debug("addFSFileLink: " + file);
			fFileInfo.add(new FileInfo(file.getAbsolutePath(), lineno));
			// TODO Auto-generated method stub
//			super.addFSFileLink(file, lineno, offset, length);
		}
		
	}

	private static class TestGenericRelPathPathMatcher extends GenericRelPathPatternMatcher {
		public List<FileInfo> 		fFileInfo = new ArrayList<FileInfo>();

		@Override
		protected void addIFileLink(IFile file, int lineno, int offset, int length) {
			System.out.println("addIFileLink: " + file);
			// TODO Auto-generated method stub
//			super.addIFileLink(file, lineno, offset, length);
		}

		@Override
		protected void addFSFileLink(File file, int lineno, int offset, int length) {
			System.out.println("addFSFileLink: " + file);
			fFileInfo.add(new FileInfo(file.getAbsolutePath(), lineno));
			// TODO Auto-generated method stub
//			super.addFSFileLink(file, lineno, offset, length);
		}
		
	}
	
	public void testNoLineNumber() {
		TestGenericPathPathMatcher matcher = new TestGenericPathPathMatcher();
		TestTextConsole console = new TestTextConsole();
		File path = new File(fTmpDir, "bar_pkg.sv");
		
		TestUtils.copy(
				"package bar_pkg;\n" +
				"	int var;\n" +
				"endpackage\n",
				path);
		
		console.addPatternMatchListener(matcher);
	
		console.getDocument().set(
				path.getAbsolutePath() + "\n");
		for (int i=0; i<100; i++) {
			try {
				Thread.sleep(10);
			} catch (InterruptedException e) {}
			if (matcher.fFileInfo.size() > 0) {
				break;
			}
		}

		assertEquals(1, matcher.fFileInfo.size());
		FileInfo info = matcher.fFileInfo.get(0);
		assertEquals(path.getAbsolutePath(), info.fPath);
		assertEquals(-1, info.fLineno);
	}

	public void testColonLineNumber() {
		TestGenericPathPathMatcher matcher = new TestGenericPathPathMatcher();
		TestTextConsole console = new TestTextConsole();
		File path = new File(fTmpDir, "bar_pkg.sv");
		
		TestUtils.copy(
				"package bar_pkg;\n" +
				"	int var;\n" +
				"endpackage\n",
				path);
		
		console.addPatternMatchListener(matcher);
	
		console.getDocument().set(
				path.getAbsolutePath() + ":20\n");
		for (int i=0; i<100; i++) {
			try {
				Thread.sleep(10);
			} catch (InterruptedException e) {}
			if (matcher.fFileInfo.size() > 0) {
				break;
			}
		}

		assertEquals(1, matcher.fFileInfo.size());
		FileInfo info = matcher.fFileInfo.get(0);
		assertEquals(path.getAbsolutePath(), info.fPath);
		assertEquals(20, info.fLineno);
	}

	public void testParenLineNumber() {
		TestGenericPathPathMatcher matcher = new TestGenericPathPathMatcher();
		TestTextConsole console = new TestTextConsole();
		File path = new File(fTmpDir, "bar_pkg.sv");
		
		TestUtils.copy(
				"package bar_pkg;\n" +
				"	int var;\n" +
				"endpackage\n",
				path);
		
		console.addPatternMatchListener(matcher);
	
		console.getDocument().set(
				path.getAbsolutePath() + "(30)\n");
		for (int i=0; i<100; i++) {
			try {
				Thread.sleep(10);
			} catch (InterruptedException e) {}
			if (matcher.fFileInfo.size() > 0) {
				break;
			}
		}

		assertEquals(1, matcher.fFileInfo.size());
		FileInfo info = matcher.fFileInfo.get(0);
		assertEquals(path.getAbsolutePath(), info.fPath);
		assertEquals(30, info.fLineno);
	}
	
	public void testCommaLineNumber() {
		TestGenericPathPathMatcher matcher = new TestGenericPathPathMatcher();
		TestTextConsole console = new TestTextConsole();
		File path = new File(fTmpDir, "bar_pkg.sv");
		
		TestUtils.copy(
				"package bar_pkg;\n" +
				"	int var;\n" +
				"endpackage\n",
				path);
		
		console.addPatternMatchListener(matcher);
	
		console.getDocument().set(
				"\"" + path.getAbsolutePath() + "\", 40\n");
		for (int i=0; i<100; i++) {
			try {
				Thread.sleep(10);
			} catch (InterruptedException e) {}
			if (matcher.fFileInfo.size() > 0) {
				break;
			}
		}

		assertEquals(1, matcher.fFileInfo.size());
		FileInfo info = matcher.fFileInfo.get(0);
		assertEquals(path.getAbsolutePath(), info.fPath);
		assertEquals(40, info.fLineno);
	}	
	
	public void testCommaLineNumberRelative() {
		TestGenericRelPathPathMatcher matcher = new TestGenericRelPathPathMatcher();
		TestTextConsole console = new TestTextConsole();
		final File foo = new File(fTmpDir, "foo");
		File path = new File(fTmpDir, "bar_pkg.sv");
		
		matcher.init(new ILogMessageScannerMgr() {
			
			@Override
			public void setWorkingDirectory(String path, ILogMessageScanner scanner) {
				// TODO Auto-generated method stub
				
			}
			
			@Override
			public String getWorkingDirectory() {
				return foo.getAbsolutePath();
			}
			
			@Override
			public void addMessage(ScriptMessage msg) {
				// TODO Auto-generated method stub
				
			}
		});
		
		foo.mkdirs();
		
		TestUtils.copy(
				"package bar_pkg;\n" +
				"	int var;\n" +
				"endpackage\n",
				path);
		
		console.addPatternMatchListener(matcher);
	
		console.getDocument().set(
				"\"../bar_pkg.sv\", 40\n");
		for (int i=0; i<100; i++) {
			try {
				Thread.sleep(10);
			} catch (InterruptedException e) {}
			if (matcher.fFileInfo.size() > 0) {
				break;
			}
		}

		assertEquals(1, matcher.fFileInfo.size());
		FileInfo info = matcher.fFileInfo.get(0);
		assertEquals(path.getAbsolutePath(), info.fPath);
		assertEquals(40, info.fLineno);
	}	
}
