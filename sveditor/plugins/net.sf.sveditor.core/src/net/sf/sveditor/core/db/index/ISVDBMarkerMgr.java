package net.sf.sveditor.core.db.index;

public interface ISVDBMarkerMgr {
	String				MARKER_TYPE_ERROR   = "ERROR";
	String				MARKER_TYPE_WARNING = "WARNING";
	String				MARKER_TYPE_INFO    = "INFO";
	String				MARKER_TYPE_TASK    = "TASK";

	void addMarker(
			String 			path,
			String			type,
			int				lineno,
			String			msg);
			
	void clearMarkers(String path);
	
}
