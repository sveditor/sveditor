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
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.index.SVDBFSFileSystemProvider;
import org.eclipse.hdt.sveditor.core.db.index.SVDBWSFileSystemProvider;
import org.eclipse.hdt.sveditor.core.log.ILogHandle;
import org.eclipse.hdt.sveditor.core.log.ILogLevel;
import org.eclipse.hdt.sveditor.core.log.ILogLevelListener;
import org.eclipse.hdt.sveditor.core.log.LogFactory;
import org.eclipse.hdt.sveditor.core.log.LogHandle;
import org.eclipse.hdt.sveditor.core.scanutils.ITextScanner;
import org.eclipse.hdt.sveditor.core.scanutils.StringTextScanner;
import org.eclipse.hdt.sveditor.core.script.launch.ScriptMessage.MessageType;

/**
 * 
 * @author ballance
 *
 * Parses NCSim-format error messages.
 * 
 * NCSim errors are multi-line:
 * <text from source file>
 * <pointer to element>
 * ncvlog: *[W|E],<MSG_CODE> (<path>,<line>,<pos>): <MSG>
 * 
 * This parser, however, only parses the ncvlog: line
 */
public class NCSimLogMessageScanner implements ILogMessageScanner, ILogLevelListener,
		ILogLevel {
	private ILogMessageScannerMgr			fMgr;
	private LogHandle						fLog;
	private boolean							fDebugEn = false;
	private SVDBWSFileSystemProvider		fFSProvider;
	
	public NCSimLogMessageScanner() {
		fLog = LogFactory.getLogHandle("NCSimLogMessageScanner");
		fFSProvider = new SVDBWSFileSystemProvider();
	}
	
	@Override
	public void init(ILogMessageScannerMgr mgr) {
		fMgr = mgr;
	}
	
	@Override
	public void close() { 
		fFSProvider.dispose();
		fFSProvider = null;
	}

	@Override
	public void logLevelChanged(ILogHandle handle) {
		fDebugEn = (handle.getDebugLevel() > 0);
	}

	@Override
	public boolean providesDirectory() {
		return false;
	}

	@Override
	public void line(String l) {
		l = l.trim();
		
		if (l.startsWith("ncvlog:")) {
			StringTextScanner scanner = new StringTextScanner(l);
			scanner.seek("ncvlog:".length());
			
			int ch = scanner.skipWhite(scanner.get_ch());
			
			if (ch != '*') {
				if (fDebugEn) {
					fLog.debug(LEVEL_MID, "mal-formed ncvlog message: " + l);
					fLog.debug(LEVEL_MID, "  Failed to find '*' prefix after ncvlog:");
				}
				return;
			}
			
			ch = scanner.get_ch();
	
			MessageType msg_type = null;
			if (ch != 'W' && ch != 'E') {
				if (fDebugEn) {
					fLog.debug(LEVEL_MID, "mal-formed ncvlog message: " + l);
					fLog.debug(LEVEL_MID, "  Failed to find 'W' or 'E' code");
				}
				return;
			} else {
				if (ch == 'W') {
					msg_type = MessageType.Warning;
				} else {
					msg_type = MessageType.Error;
				}
			}
		
			while ((ch = scanner.get_ch()) != -1 && ch != '(') { ; }
			
			if (ch != '(') {
				if (fDebugEn) {
					fLog.debug(LEVEL_MID, "failed to find start of NCsim-style path in message " + l);
				}
				return;
			}
			
			Tuple<String, Integer> path = parsePath(scanner);
			
			if (path == null || path.first() == null || path.second() == -1) {
				if (fDebugEn) {
					fLog.debug(LEVEL_MID, "failed to find path in message " + l);
				}
				return;
			}
			
			// Now, find the message
			ch = scanner.get_ch();
			
			if (ch != ':') {
				if (fDebugEn) {
					fLog.debug(LEVEL_MID, "failed to locate ':' before message in line " + l +
							" (post-path character is " + (char)ch + ")");
				}
			}
			
			ch = scanner.skipWhite(scanner.get_ch());
			
			String message = LogMessageScannerUtils.readLine(scanner, ch);
		
			String path_s = SVFileUtils.resolvePath(
					path.first(), 
					fMgr.getWorkingDirectory(), 
					new SVDBFSFileSystemProvider(), false);

			ScriptMessage msg = new ScriptMessage(
					path_s, path.second(), message, msg_type);
			msg.setMarkerType(SVCorePlugin.SV_PROBLEM);
			fMgr.addMessage(msg);
		}
	}

	private Tuple<String, Integer> parsePath(ITextScanner scanner) {
		int ch = scanner.skipWhite(scanner.get_ch());
		
		String path = LogMessageScannerUtils.readPath(scanner, ch);
		int lineno = -1;
		
		ch = scanner.get_ch();
		
		if (ch == ',') {
			lineno = LogMessageScannerUtils.readInt(
					scanner, scanner.get_ch());
			
			// Should be the trailing '|'
			ch = scanner.get_ch();
			
			// Need to read forward to ')'
			while ((ch = scanner.get_ch()) != -1 && ch != ')') {
				;
			}
		}
	
		return new Tuple<String, Integer>(path, lineno);
	}
}
