/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.ui.script.launch;

import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.db.index.SVDBWSFileSystemProvider;
import org.eclipse.hdt.sveditor.core.script.launch.ILogMessageScanner;
import org.eclipse.hdt.sveditor.core.script.launch.ILogMessageScannerMgr;
import org.eclipse.ui.console.TextConsole;

public class GenericRelPathPatternMatcher extends GenericPathPatternMatcher implements ILogMessageScanner {
	private ILogMessageScannerMgr		fMgr;
	private SVDBWSFileSystemProvider	fFS;

	@Override
	public void line(String l) { }

	@Override
	public void init(ILogMessageScannerMgr mgr) {
		fMgr = mgr;
	}

	@Override
	public boolean providesDirectory() {
		return false;
	}

	@Override
	public void close() { }

	@Override
	public void connect(TextConsole console) {
		super.connect(console);
		fFS = new SVDBWSFileSystemProvider();
	}

	@Override
	public void disconnect() {
		if (fFS != null) {
			fFS.dispose();
			fFS = null;
		}
	}
	
//	@Override
//	public void matchFound(PatternMatchEvent event) {
//		String content = null;
//		String path = null;
//		try {
//			content = fConsole.getDocument().get(event.getOffset(), event.getLength());
//		} catch (BadLocationException e) {}
//		
//		if (content == null) {
//			return;
//		}
//		
//		content = content.trim();
//		path = content;
//		
//		int paren_idx=-1;
//		int colon_idx=-1;
//		int comma_idx=-1;
//		int sp_idx=-1;
//		int lineno=-1;
//	
//		if (SVFileUtils.isWin()) {
//			content = content.replace('\\', '/');
//			
//			// Recognize MinGW-style paths: /c/foo/path
//			// Convert to Windows-type path: c:/foo/path
////			if (content.length() >= 3 && 
////					(content.charAt(0) == '/') &&
////					(content.charAt(2) == '/')) {
////				int ch = Character.toLowerCase(content.charAt(1));
////				
////				if (ch >= 'a' && ch <= 'z') {
////					content = content.charAt(1) + ":" + content.substring(2);
////				}
////			}
//		}
//	
//		
//		if ((paren_idx=content.indexOf('(')) != -1) {
//			int end_idx=paren_idx+1;
//			
//			while (end_idx<content.length() && 
//					Character.isDigit(content.charAt(end_idx))) {
//				end_idx++;
//			}
//			
//			String number = (end_idx<content.length())?
//					content.substring(paren_idx+1,end_idx):
//						content.substring(paren_idx+1);
//					
//			path = content.substring(0,paren_idx);
//			
//			try {
//				lineno = Integer.parseInt(number);
//			} catch (NumberFormatException e) {}
//			// Look for a line number after a comma (/path/file.sv,10)
//		} else if ((comma_idx=content.indexOf(',')) != -1) {
//			
//		} else if ((colon_idx=content.indexOf(':')) != -1) {
//			if (colon_idx != 1 || (colon_idx=content.indexOf(':',colon_idx+1)) != -1) {
//				int end_idx=colon_idx+1;
//
//				while (end_idx<content.length() && 
//						Character.isDigit(content.charAt(end_idx))) {
//					end_idx++;
//				}
//
//				String number = (end_idx<content.length())?
//						content.substring(colon_idx+1,end_idx):
//							content.substring(colon_idx+1);
//
//				content = content.substring(0,colon_idx);
//
//				try {
//					lineno = Integer.parseInt(number);
//				} catch (NumberFormatException e) {}			
//			}
//		} else if ((sp_idx=content.indexOf(' ')) != -1) {
//			// See if there's a trailing number.
//			int idx = sp_idx;
//			while (idx < content.length() && 
//					Character.isWhitespace(content.charAt(idx))) {
//				idx++;
//			}
//			
//			if (idx < content.length() && 
//					content.charAt(idx) >= '0' && content.charAt(idx) <= '9') {
//				String number = content.substring(idx).trim();
//				content = content.substring(0, sp_idx);
//				try {
//					lineno = Integer.parseInt(number);
//				} catch (NumberFormatException e) {
//					e.printStackTrace();
//				}
//			}
//		}
//
//		String path = content;
//		if (fMgr != null) {
//			path = SVFileUtils.resolvePath(
//					path, 
//					fMgr.getWorkingDirectory(), 
//					fFS, true);
//		}
//		
//		IFile file = SVFileUtils.findWorkspaceFile(path);
//		File efile = SVFileUtils.getFile(content);
//	
//		// Eclipse sometimes returns a file (that doesn't exist) for
//		// a directory path. We only want to hyperlink 'real' files.
//		if (file != null && file.exists()) {
//			FileLink link = new FileLink(file, null, -1, -1, lineno);
//			try {
//				fConsole.addHyperlink(link, event.getOffset(), content.length());
//			} catch (BadLocationException e) {}
//		} else if (efile != null && efile.isFile()) {
//			IFileStore fs = EFS.getLocalFileSystem().getStore(new Path(efile.getAbsolutePath()));
//			ExternalPathHyperlink link = new ExternalPathHyperlink(fs, null, -1, -1, lineno);
//			try {
//				fConsole.addHyperlink(link, event.getOffset(), content.length());
//			} catch (BadLocationException e) {}
//		}
//	}
	
	protected String resolvePath(String path) {
		if (fMgr != null) {
			path = SVFileUtils.resolvePath(
					path, 
					fMgr.getWorkingDirectory(), 
					fFS, true);
		}

		return path;
	}

	@Override
	public String getPattern() {
		return "\"?\\.\\.[/\\\\][^ \\t\\n\\r]+\"?,?([ \\t]+[0-9]+)?";
	}

	@Override
	public int getCompilerFlags() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public String getLineQualifier() {
		// TODO Auto-generated method stub
		return null;
	}
}
