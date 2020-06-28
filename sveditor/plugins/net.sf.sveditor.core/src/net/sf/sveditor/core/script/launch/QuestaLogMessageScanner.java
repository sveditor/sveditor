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

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.script.launch.ScriptMessage.MessageType;

/**
 * 
 * @author ballance
 *
 * Parses Questa-format error messages.
 * 
 * Two basic formats are supported:
 * - Single-line
 *   - ** Error (suppressible): <path>(<lineno>): <message>
 *   - ** Error (suppressible): (vopt-XXXX) <path>(<lineno>): <message>
 *   
 * - Multi-line
 *   - ** Error: ** while parsing ... at <path1>(<lineno>)
 *     ** while ...: ... at: <path>(<lineno>)
 *     ** at <path>(<lineno>): <message>
 */
public class QuestaLogMessageScanner implements ILogMessageScanner, ILogLevelListener,
		ILogLevel {
	private ILogMessageScannerMgr			fMgr;
	private ScriptMessage					fMultiLineMsg;
	private LogHandle						fLog;
	private boolean							fDebugEn = false;
	private SVDBWSFileSystemProvider		fFSProvider;
	
	public QuestaLogMessageScanner() {
		fLog = LogFactory.getLogHandle("QuestaLogMessageScanner");
		fLog.addLogLevelListener(this);
	}
	
	@Override
	public void init(ILogMessageScannerMgr mgr) {
		fMgr = mgr;
		fFSProvider = new SVDBWSFileSystemProvider();
	}
	
	@Override
	public void close() {
		if (fMultiLineMsg != null && fMultiLineMsg.isValid()) {
			fMgr.addMessage(fMultiLineMsg);
		}
		fMultiLineMsg = null;
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

		if (fMultiLineMsg != null) {
			if (l.startsWith("** while")) {
				// This is a continuation, but one we don't really care about
				// TODO: add in hyperlinks
			} else if (l.startsWith("** at")) {
				// This is where the most-proximate message is
				StringTextScanner scanner = new StringTextScanner(l);
				scanner.seek("** at.".length());

				int path_start = scanner.getOffset();
				Tuple<String, Integer> path_line = parsePath(scanner);
				fMultiLineMsg.setPath(path_line.first());
				fMultiLineMsg.setLineno(path_line.second());
				int path_end = scanner.getOffset();

//				ScriptHyperlink link = new ScriptHyperlink(
//						path_line.first(), path_start, (path_end-path_start));
//				link.setLineno(path_line.second());
//				fMgr.addHyperlink(link);
			
				// Assume this is ':'
				int ch = scanner.skipWhite(scanner.get_ch());
				
				if (ch != ':') {
					if (fDebugEn) {
					fLog.debug(LEVEL_MID, "Expecting ':' after path " + path_line.first() +
							" received " + (char)ch + " instead");
					}
				}
				
				ch = scanner.skipWhite(scanner.get_ch());
				
				if (ch == '(') {
					ch = scanner.skipPastMatch("()");
					ch = scanner.skipWhite(ch);
				}
				
				String msg = LogMessageScannerUtils.readLine(scanner, ch);
			
				fMultiLineMsg.setMessage(msg);
				
				fMgr.addMessage(fMultiLineMsg);
				
				fMultiLineMsg = null;
			} else {
				// This is not a continuation
				if (fMultiLineMsg.isValid()) {
					fMgr.addMessage(fMultiLineMsg);
				}
				fMultiLineMsg = null;
			}
		} else if (l.startsWith("** Error:") || l.startsWith("** Error (")) {
			// Likely a Questa error
			StringTextScanner scanner = new StringTextScanner(l);
			scanner.seek("** Error:".length());
			MessageType type = (l.startsWith("** Error"))?MessageType.Error:MessageType.Warning;
			
			int colon_index = l.indexOf(':');
			int paren_index = l.indexOf('(');
		
			int ch;
			if (paren_index != -1 && paren_index < colon_index) {
				// Skip the suppressible element
				ch = scanner.skipWhite(scanner.get_ch());
				if (ch == '(') {
					ch = scanner.skipPastMatch("()");
				}
			
				// ch should be ':', which we'll just let go
			}
			
			ch = scanner.skipWhite(scanner.get_ch());
			
			if (ch == '*') {
				// This should be a "** while parsing ..." message
				ch = scanner.get_ch();
				
				if (ch != '*') {
					if (fDebugEn) {
					fLog.debug(LEVEL_MID, 
							"Expecting second '*' for a 'while parsing' message. Received " +
									(char)ch + " instead");
					}
				} else {
					fMultiLineMsg = new ScriptMessage(null, -1, null, type);
					fMultiLineMsg.setMarkerType(SVCorePlugin.PLUGIN_ID + ".svProblem");
				}
			} else {
				// Should be a normal message
			
				if (ch == '(') {
					// very likely a tool code like vopt-<XXXX>
					ch = scanner.skipPastMatch("()");
				}

				ch = scanner.skipWhite(ch);
				scanner.unget_ch(ch);

				int path_start = scanner.getOffset();
				Tuple<String, Integer> path_line = parsePath(scanner);
				int path_end = scanner.getOffset();
				String path = path_line.first();
				int lineno = path_line.second();
				
//				ScriptHyperlink link = new ScriptHyperlink(
//						path_line.first(), path_start, (path_end-path_start));
//				link.setLineno(lineno);
//				fMgr.addHyperlink(link);

				ch = scanner.get_ch();

				// Should be ':'
				if ((ch = scanner.get_ch()) != ':') {
					scanner.unget_ch(ch);
				}

				if (path != null && lineno != -1) {
					path = SVFileUtils.resolvePath(path, fMgr.getWorkingDirectory(), 
							fFSProvider, false);

					// Read the remainder of the line as the message
					ch = scanner.skipWhite(scanner.get_ch());
					String message = LogMessageScannerUtils.readLine(scanner, ch);
					ScriptMessage msg = new ScriptMessage(path, lineno, message, MessageType.Error);
					msg.setMarkerType(SVCorePlugin.PLUGIN_ID + ".svProblem");

					fMgr.addMessage(msg);
				}
			}
		}
	}

	private Tuple<String, Integer> parsePath(ITextScanner scanner) {
		int ch = scanner.skipWhite(scanner.get_ch());
		
		String path = LogMessageScannerUtils.readPath(scanner, ch);
		int lineno = -1;
		
		ch = scanner.get_ch();
		
		if (ch == '(') {
			lineno = LogMessageScannerUtils.readInt(
					scanner, scanner.get_ch());
			
			// Shoould be the trailing  ')'
			ch = scanner.get_ch();
		}
	
		return new Tuple<String, Integer>(path, lineno);
	}
}
