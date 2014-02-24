package net.sf.sveditor.core.db.index;

import java.util.List;

import net.sf.sveditor.core.db.SVDBMarker;

public interface ISVDBMarkerFinder {

	List<SVDBMarker> getMarkers(String path);
	
}
