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
package org.eclipse.hdt.sveditor.core.script.launch;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.SVFileUtils;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.eclipse.hdt.sveditor.core.db.index.SVDBFSFileSystemProvider;
import org.eclipse.hdt.sveditor.core.scanutils.StringTextScanner;
import org.eclipse.hdt.sveditor.core.script.launch.ScriptMessage.MessageType;

public class VerilatorLogMessageScanner implements ILogMessageScanner {
	private ILogMessageScannerMgr		fMgr;
	private ISVDBFileSystemProvider		fFSProvider;
	
	public VerilatorLogMessageScanner() {
		fFSProvider = new SVDBFSFileSystemProvider();
	}

	@Override
	public void line(String l) {
		l = l.trim();
		
		if (l.startsWith("%Error") || l.startsWith("%Warning")) {
			MessageType type = (l.startsWith("%Error"))?MessageType.Error:MessageType.Warning;
		
			StringTextScanner scanner = new StringTextScanner(l);
			
			// Find the end of the prefix
			int ch;
			
			while ((ch = scanner.get_ch()) != -1 && ch != ':') {
				;
			}
			
			if (ch == -1) {
				return;
			}
			
			ch = scanner.skipWhite(scanner.get_ch());
			
			String path = LogMessageScannerUtils.readPath(scanner, ch);
			int lineno = -1;
			
			ch = scanner.get_ch();
			
			if (ch == ':') {
				ch = scanner.get_ch();
				lineno = LogMessageScannerUtils.readInt(scanner, ch);
				// Skip trailing ':'
				ch = scanner.get_ch();
			}
		
	
			if (path != null && lineno != -1) {
				path = SVFileUtils.resolvePath(path, fMgr.getWorkingDirectory(), 
						fFSProvider, false);
				
				ch = scanner.skipWhite(scanner.get_ch());
				String message = LogMessageScannerUtils.readLine(scanner, ch);
				
				ScriptMessage msg = new ScriptMessage(path, lineno, message, type);
				msg.setMarkerType(SVCorePlugin.PLUGIN_ID + ".svProblem");
				fMgr.addMessage(msg);
			}
		}
	}

	@Override
	public void init(ILogMessageScannerMgr mgr) {
		fMgr = mgr;
	}
	
	@Override
	public void close() { }

	@Override
	public boolean providesDirectory() {
		return false;
	}

}
