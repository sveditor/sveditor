package net.sf.sveditor.core.script.launch;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.ILineListener;
import net.sf.sveditor.core.log.ILogLevel;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class LogMessageScannerMgr implements ILogMessageScannerMgr, ILineListener,
		ILogLevel {
	private LogHandle						fLog;
	private String							fWorkingDir;
	private List<ILogMessageScanner>		fScanners;
	private List<ScriptMessage>				fMessages;
	private List<ILogMessageListener>		fMessageListeners;
	
	public LogMessageScannerMgr(String working_dir) {
		fWorkingDir = working_dir;
		fScanners = new ArrayList<ILogMessageScanner>();
		fMessages = new ArrayList<ScriptMessage>();
		fMessageListeners = new ArrayList<ILogMessageListener>();
		fLog = LogFactory.getLogHandle("LogMessageScannerMgr");
	}
	
	public void addMessageListener(ILogMessageListener l) {
		fMessageListeners.add(l);
	}
	
	public void addScanner(ILogMessageScanner scanner) {
		scanner.init(this);
		fScanners.add(scanner);
	}

	public List<ScriptMessage> getMessages() {
		return fMessages;
	}
	
	public void setWorkingDirectory(String path) {
		fWorkingDir = path;
	}

	@Override
	public void setWorkingDirectory(String path, ILogMessageScanner scanner) {
		fWorkingDir = path;
	}

	@Override
	public String getWorkingDirectory() {
		return fWorkingDir;
	}

	@Override
	public void addMessage(ScriptMessage msg) {
		fLog.debug(LEVEL_MID, "addMessage: " + msg.getMarkerType() + " " +
				msg.getPath() + ":" + msg.getLineno() + " " + msg.getMessage());
		if (fMessageListeners.size() > 0) {
			for (int i=0; i<fMessageListeners.size(); i++) {
				fMessageListeners.get(i).message(msg);
			}
		} else {
			fMessages.add(msg);
		}
	}
	
	@Override
	public void line(String l) {
		synchronized (fScanners) {
			// First, provide the line to any scanners that might change
			// the working directory
			for (ILogMessageScanner s : fScanners) {
				if (s.providesDirectory()) {
					s.line(l);
				}
			}
			
			// Then, provide the line to scanners that won't change the
			// working directory
			for (ILogMessageScanner s : fScanners) {
				if (!s.providesDirectory()) {
					s.line(l);
				}
			}
		}
	}
	
	public void close() {
		synchronized (fScanners) {
			for (ILogMessageScanner s : fScanners) {
				s.close();
			}
		}
	}
}
