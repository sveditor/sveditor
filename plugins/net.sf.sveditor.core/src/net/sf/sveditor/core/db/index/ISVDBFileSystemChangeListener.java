package net.sf.sveditor.core.db.index;

public interface ISVDBFileSystemChangeListener {
	
	void fileChanged(String path);
	
	void fileRemoved(String path);
	
	void fileAdded(String path);

}
