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

public class GccLogMessageScanner implements ILogMessageScanner {
	private ILogMessageScannerMgr			fMgr;
	private ISVDBFileSystemProvider			fFSProvider;
	private ScriptMessage					fMultiLineMsg;
	
	public GccLogMessageScanner() {
		fFSProvider = new SVDBFSFileSystemProvider();
	}

	@Override
	public void close() {
		if (fMultiLineMsg != null) {
			fMgr.addMessage(fMultiLineMsg);
		}
		fMultiLineMsg = null;
	}

	@Override
	public void line(String l) {
		int err_idx, warn_idx;
		
		l = l.trim();
		if ((err_idx = l.indexOf(" error: ")) != -1 ||
				(warn_idx = l.indexOf(" warning: ")) != -1) {
			StringTextScanner s1 = new StringTextScanner(l);
		
			int ch;
			
			String path = LogMessageScannerUtils.readPath(s1, s1.get_ch());
			int lineno;
		
			ch = s1.get_ch(); // :
			lineno = LogMessageScannerUtils.readInt(s1, s1.get_ch());
			
			StringTextScanner s2;
			
			if (err_idx != -1) {
				s2 = new StringTextScanner(
						l.substring(err_idx + " error: ".length()));
			} else {
				s2 = new StringTextScanner(
						l.substring(err_idx + " warning: ".length()));
			}
			
			ch = s2.skipWhite(s2.get_ch());
			
			String message = LogMessageScannerUtils.readLine(s2, ch);
			
			if (path != null && lineno != -1 && message != null) {
				path = SVFileUtils.resolvePath(path, fMgr.getWorkingDirectory(), fFSProvider, false);
				
				ScriptMessage msg = new ScriptMessage(path, lineno, message, 
						(err_idx != -1)?MessageType.Error:MessageType.Warning);
				msg.setMarkerType(SVCorePlugin.PLUGIN_ID + ".gccProblem");
				fMgr.addMessage(msg);
			}
			
		}

	}

	@Override
	public void init(ILogMessageScannerMgr mgr) {
		fMgr = mgr;
	}

	@Override
	public boolean providesDirectory() {
		return false;
	}

}
