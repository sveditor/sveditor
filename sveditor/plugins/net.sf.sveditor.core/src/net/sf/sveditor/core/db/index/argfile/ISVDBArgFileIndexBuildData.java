package net.sf.sveditor.core.db.index.argfile;

import java.util.List;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBFileTree;
import net.sf.sveditor.core.db.SVDBMarker;

import org.eclipse.core.runtime.IProgressMonitor;

public interface ISVDBArgFileIndexBuildData {
	
	void removeFile(String path, boolean is_argfile);
	
	SVDBFile getFile(IProgressMonitor monitor, String path);

	void setFile(String path, SVDBFile file, boolean is_argfile);
	void setLastModified(String path, long timestamp, boolean is_argfile);
	void setMarkers(String path, List<SVDBMarker> markers, boolean is_argfile);
	List<SVDBMarker> getMarkers(String path);
	void setFileTree(String path, SVDBFileTree file, boolean is_argfile);
	
	void addIncludePath(String path);
	
	void addDefine(String key, String val);
	
	void setMFCU();
	
	boolean isMFCU();

	void setForceSV(boolean force);
	
	boolean getForceSV();
	
	void addLibFile(String path);
	
}
