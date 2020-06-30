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
package org.eclipse.hdt.sveditor.ui.console;

import java.io.File;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.ui.console.PatternMatchEvent;

public class WorkspacePathPatternMatcher extends SVPatternMatcherBase {
	
	@Override
	public void matchFound(PatternMatchEvent event) {
		String content = null;
		try {
			content = fConsole.getDocument().get(event.getOffset(), event.getLength());
		} catch (BadLocationException e) {}
	
		if (content == null) {
			return;
		}
		
		content = content.trim();
		
		int paren_idx=-1;
		int colon_idx=-1;
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
		
		if ((paren_idx=content.indexOf('(')) != -1) {
			int end_idx=paren_idx+1;
			
			while (end_idx<content.length() && 
					Character.isDigit(content.charAt(end_idx))) {
				end_idx++;
			}
			
			String number = (end_idx<content.length())?
					content.substring(paren_idx+1,end_idx):
						content.substring(paren_idx+1);
					
			content = content.substring(0,paren_idx);
			
			try {
				lineno = Integer.parseInt(number);
			} catch (NumberFormatException e) {}
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

				content = content.substring(0,colon_idx);

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
				content = content.substring(0, sp_idx);
				try {
					lineno = Integer.parseInt(number);
				} catch (NumberFormatException e) {
					e.printStackTrace();
				}
			}
		}

		IContainer c = SVFileUtils.findWorkspaceFolder(content);
		if (c == null) {
			// Must ensure that we're not dealing with a folder
			IFile file = SVFileUtils.findWorkspaceFile(content);
			File efile = SVFileUtils.getFile(content);
	
			// Eclipse sometimes returns a file (that doesn't exist) for
			// a directory path. We only want to hyperlink 'real' files.
			if (file != null && file.exists()) {
				addIFileLink(file, lineno, event.getOffset(), content.length());
			} else if (efile != null && efile.isFile()) {
				addFSFileLink(efile, lineno, event.getOffset(), content.length());
			}
		}
	}

	@Override
	public String getPattern() {
		return "\\$\\{workspace_loc\\}[/\\\\][^ \\t\\r\\n]+([ \\t]+[0-9]+)?";
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
