package net.sf.sveditor.core.script.launch;

public class ScriptMessage {
	public enum MessageType {
		Note,
		Warning,
		Error
	}

	private String				fMarkerType;
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
		fMarkerType = null;
	}
	
	public boolean isValid() {
		return (fPath != null && fMessage != null &&
				fLineno != -1);
	}
	
	public void setMarkerType(String type) {
		fMarkerType = type;
	}
	
	public String getMarkerType() {
		return fMarkerType;
	}
	
	public String getMessage() {
		return fMessage;
	}
	
	public void setMessage(String msg) {
		fMessage = msg;
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
	
	public void setPath(String path) {
		fPath = path;
	}
	
	public int getLineno() {
		return fLineno;
	}
	
	public void setLineno(int lineno) {
		fLineno = lineno;
	}
	
	public MessageType getType() {
		return fType;
	}
	
}
