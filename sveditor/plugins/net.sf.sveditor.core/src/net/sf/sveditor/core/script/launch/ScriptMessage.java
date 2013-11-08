package net.sf.sveditor.core.script.launch;

public class ScriptMessage {
	public enum MessageType {
		Note,
		Warning,
		Error
	}
	
	private String				fMessage;
	private String				fDescription;
	private String				fPath;
	private int					fLineno;
	private MessageType			fType;
	
	public ScriptMessage(
			String			path,
			int				lineno,
			String			message,
			MessageType		type) {
		fPath = path;
		fLineno = lineno;
		fMessage = message;
		fType = type;
	}
	
	public String getMessage() {
		return fMessage;
	}
	
	public void setDescription(String d) {
		fDescription = d;
	}
	
	public String getDescription() {
		return fDescription;
	}

	public String getPath() {
		return fPath;
	}
	
	public int getLineno() {
		return fLineno;
	}
	
	public MessageType getType() {
		return fType;
	}
	
}
