package net.sf.sveditor.core.db.index;

public class SVDBArgFileIndexCacheData extends SVDBBaseIndexCacheData {
	
	private long					fArgFileTimestamp;
	
	public SVDBArgFileIndexCacheData() {
		fArgFileTimestamp = -1;
	}
	
	public long getArgFileTimestamp() {
		return fArgFileTimestamp;
	}
	
	public void setArgFileTimestamp(long ts) {
		fArgFileTimestamp = ts;
	}

}
