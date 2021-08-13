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

import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.ui.console.PatternMatchEvent;

import org.eclipse.hdt.sveditor.ui.console.SVPatternMatcherBase;

public class GenericPathPatternMatcher extends SVPatternMatcherBase {
	
	@Override
	public void matchFound(PatternMatchEvent event) {
		String content = null;
		String path = null;
		try {
			content = fConsole.getDocument().get(event.getOffset(), event.getLength());
		} catch (BadLocationException e) {}
		
		if (content == null) {
			return;
		}
		
		content = content.trim();
		path = content; // we fall through if no line numbers are detected
		
		int paren_idx=-1;
		int colon_idx=-1;
		int comma_idx=-1;
		int lineno=-1;
		int sp_idx=-1;
	
		if (SVFileUtils.isWin()) {
			content = content.replace('\\', '/');
			
			// Recognize MinGW-style paths: /c/foo/path
			// Convert to Windows-type path: c:/foo/path
			if (content.length() >= 3 && 
					(content.charAt(0) == '/') &&
					(content.charAt(2) == '/')) {
				int ch = Character.toLowerCase(content.charAt(1));
				
				if (ch >= 'a' && ch <= 'z') {
					content = content.charAt(1) + ":" + content.substring(2);
				}
			}
		}
	
		// Look for a line number in parens (/path/file.sv (10))
		if ((paren_idx=content.indexOf('(')) != -1) {
			int end_idx=paren_idx+1;
			
			while (end_idx<content.length() && 
					Character.isDigit(content.charAt(end_idx))) {
				end_idx++;
			}
			
			String number = (end_idx<content.length())?
					content.substring(paren_idx+1,end_idx):
						content.substring(paren_idx+1);
					
			path = content.substring(0,paren_idx);
			
			try {
				lineno = Integer.parseInt(number);
			} catch (NumberFormatException e) {}
		// Look for a line number after a comma (/path/file.sv,10)
		} else if ((comma_idx=content.indexOf(',')) != -1) {
			path = content.substring(0, comma_idx);
			comma_idx++;
			
			// Skip any whitespace
			while (comma_idx<content.length() && 
					Character.isWhitespace(content.charAt(comma_idx))) {
				comma_idx++;
			}
		
			// Now search to the end of the number
			int end_idx=comma_idx;
			
			while (end_idx<content.length() && 
					Character.isDigit(content.charAt(end_idx))) {
				end_idx++;
			}
			
			if (end_idx != comma_idx && end_idx <= content.length()) {
				String number = content.substring(comma_idx, end_idx);
				
				try {
					lineno = Integer.parseInt(number);
				} catch (NumberFormatException e) {}
			}
		// Look for a line number after a colon (/path/file.sv:10)
		} else if ((colon_idx=content.indexOf(':')) != -1) {
			if (colon_idx != 1 || (colon_idx=content.indexOf(':',colon_idx+1)) != -1) {
				int end_idx=colon_idx+1;

				while (end_idx<content.length() && 
						Character.isDigit(content.charAt(end_idx))) {
					end_idx++;
				}

				String number = (end_idx<content.length())?
						content.substring(colon_idx+1,end_idx):
							content.substring(colon_idx+1);

				path = content.substring(0,colon_idx);

				try {
					lineno = Integer.parseInt(number);
				} catch (NumberFormatException e) {}			
			}
		} else if ((sp_idx=content.indexOf(' ')) != -1) {
			// See if there's a trailing number.
			int idx = sp_idx;
			while (idx < content.length() && 
					Character.isWhitespace(content.charAt(idx))) {
				idx++;
			}
			
			if (idx < content.length() && 
					content.charAt(idx) >= '0' && content.charAt(idx) <= '9') {
				String number = content.substring(idx).trim();
				path = content.substring(0, sp_idx);
				try {
					lineno = Integer.parseInt(number);
				} catch (NumberFormatException e) {
					e.printStackTrace();
				}
			}
		}

		if (path != null) {
			path = path.trim();
			if (path.length() > 0) {
				if (path.charAt(0) == '"' && path.length() > 1) {
					path = path.substring(1, path.length()-1);
				}
			
				// Perform any resolution (eg resolve relative paths)
				path = resolvePath(path);
				
				IFile file = SVFileUtils.findWorkspaceFile(path);
				File efile = SVFileUtils.getFile(path);

				// Eclipse sometimes returns a file (that doesn't exist) for
				// a directory path. We only want to hyperlink 'real' files.
				if (file != null && file.exists()) {
					addIFileLink(file, lineno, event.getOffset(), content.length());
				} else if (efile != null && efile.isFile()) {
					addFSFileLink(efile, lineno, event.getOffset(), content.length());
				}
			}
		}
	}
	
	protected String resolvePath(String path) {
		// By default, no resolution is needed
		return path;
	}

	@Override
	public String getPattern() {
		return "\"?([a-zA-Z]:)?[/\\\\][^ \\t\\r\\n]+\"?,?([ \\t]+[0-9]+)?";
	}

}
