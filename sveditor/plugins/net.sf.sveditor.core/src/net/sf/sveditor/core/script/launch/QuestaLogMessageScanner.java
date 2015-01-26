package net.sf.sveditor.core.script.launch;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.log.ILogHandle;
import net.sf.sveditor.core.log.ILogLevelListener;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.script.launch.ScriptMessage.MessageType;

public class QuestaLogMessageScanner implements ILogMessageScanner, ILogLevelListener {
	private ILogMessageScannerMgr			fMgr;
	private List<ScriptMessage>				fMessages;
	private LogHandle						fLog;
	private boolean							fDebugEn = false;
	
	public QuestaLogMessageScanner() {
		fMessages = new ArrayList<ScriptMessage>();
		fLog = LogFactory.getLogHandle("QuestaLogMessageScanner");
	}
	
	@Override
	public void init(ILogMessageScannerMgr mgr) {
		fMessages.clear();
		fMgr = mgr;
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
		
		if (l.startsWith("** Error:") || l.startsWith("** Error (")) {
			// Likely a Questa error
			StringTextScanner scanner = new StringTextScanner(
					l.substring("** Error:".length()));
			
			int colon_index = l.indexOf(':');
			int paren_index = l.indexOf('(');
		
			int ch;
			if (paren_index != -1 && paren_index < colon_index) {
				// l.startsWith("** Error (")) {

				// Skip the suppressible element
				ch = scanner.skipWhite(scanner.get_ch());
				if (ch == '(') {
					ch = scanner.skipPastMatch("()");
				}
			
				// ch should be ':', which we'll just let go
			}
			
			ch = scanner.skipWhite(scanner.get_ch());
			
			if (ch == '(') {
				// very likely a tool code like vopt-<XXXX>
				ch = scanner.skipPastMatch("()");
			}
			
			ch = scanner.skipWhite(ch);

			String path = LogMessageScannerUtils.readPath(scanner, ch);
			int lineno = -1;

			ch = scanner.get_ch();
			
			if (ch == '(') {
				// Get the line number
				ch = scanner.get_ch();
				
				lineno = LogMessageScannerUtils.readInt(scanner, ch);
				
				// Should be the trailing ')'
				ch = scanner.get_ch();
				
				// Should be ':'
				ch = scanner.get_ch();
				
				if (ch != ':') {
					scanner.unget_ch(ch);
				}
			} else {
				scanner.unget_ch(ch);
			}
			
			if (path != null && lineno != -1) {
				path = SVFileUtils.resolvePath(path, fMgr.getWorkingDirectory(), 
						new SVDBFSFileSystemProvider(), false);
			
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
