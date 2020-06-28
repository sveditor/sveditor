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
package net.sf.sveditor.core.script.launch;

import java.util.Stack;

import net.sf.sveditor.core.scanutils.StringTextScanner;

public class MakefileLogMessageScanner implements ILogMessageScanner {
	private ILogMessageScannerMgr		fMgr;
	private Stack<String>				fPathStack;
	
	public MakefileLogMessageScanner() {
		fPathStack = new Stack<String>();
	}

	@Override
	public void line(String l) {
		l = l.trim();
		
		if (l.startsWith("make")) {
			int colon_idx = l.indexOf(':');
			
			if (colon_idx != -1) {
				StringTextScanner scanner = 
						new StringTextScanner(l.substring(colon_idx+1));
		
				int ch;
				
				ch = scanner.skipWhite(scanner.get_ch());
			
				String s = scanner.readIdentifier(ch);
				
				if (s == null) {
					return;
				}
				
				if (s.equals("Entering")) {
					while ((ch = scanner.get_ch()) != -1 && ch != '\'') { ; }
					
					if (ch == -1) {
						return;
					}
					
					String path = LogMessageScannerUtils.readPath(
							scanner, scanner.get_ch());
					
					if (path != null) {
						fPathStack.push(path);
						fMgr.setWorkingDirectory(path, this);
					}
				} else if (s.equals("Leaving")) {
					if (fPathStack.size() > 0) {
						fPathStack.pop();
					}
					
					if (fPathStack.size() > 0) {
						fMgr.setWorkingDirectory(fPathStack.peek(), this);
					}
				}
			}
		}

	}

	@Override
	public void init(ILogMessageScannerMgr mgr) {
		fMgr = mgr;
		fPathStack.clear();
		fPathStack.push(fMgr.getWorkingDirectory());
	}
	
	@Override
	public void close() { }

	@Override
	public boolean providesDirectory() {
		return true;
	}

}
