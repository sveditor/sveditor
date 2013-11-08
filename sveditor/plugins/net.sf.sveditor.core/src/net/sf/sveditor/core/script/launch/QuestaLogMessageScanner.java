package net.sf.sveditor.core.script.launch;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVFileUtils;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.scanutils.StringTextScanner;
import net.sf.sveditor.core.script.launch.ScriptMessage.MessageType;

public class QuestaLogMessageScanner implements ILogMessageScanner {
	private ILogMessageScannerMgr			fMgr;
	private List<ScriptMessage>				fMessages;
	
	public QuestaLogMessageScanner() {
		fMessages = new ArrayList<ScriptMessage>();
	}
	
	@Override
	public void init(ILogMessageScannerMgr mgr) {
		fMessages.clear();
		fMgr = mgr;
	}
	
	@Override
	public boolean providesDirectory() {
		return false;
	}

	@Override
	public void line(String l) {
		l = l.trim();

		if (l.startsWith("** Error:")) {
			System.out.println("line starts with Error");
			// Likely a Questa error
			StringTextScanner scanner = new StringTextScanner(
					l.substring("** Error:".length()));
			
			int ch = scanner.skipWhite(scanner.get_ch());
			
			if (ch == '(') {
				// very likely a tool code like vopt-<XXXX>
				ch = scanner.skipPastMatch("()");
			}

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
				String message = LogMessageScannerUtils.readLine(scanner, scanner.get_ch());
				ScriptMessage msg = new ScriptMessage(path, lineno, message, MessageType.Error);
			
				fMgr.addMessage(msg);
			}
		}
	}
	
}
