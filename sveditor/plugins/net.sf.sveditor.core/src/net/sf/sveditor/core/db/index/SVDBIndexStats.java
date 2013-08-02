package net.sf.sveditor.core.db.index;

/**
 * Provides some information on what an index is managing
 * and indexing performance
 * 
 * @author ballance
 *
 */
public class SVDBIndexStats {
	private int					fNumRootFiles;
	private int					fNumTotalFiles;

	/**
	 * Total number of processed files (includes multiple inclusions)
	 */
	private int					fNumProcessedFiles;
	
	/**
	 * Total number of lines managed by this index
	 */
	private int					fNumLines;
	
	/**
	 * Number of ms taken to read files during the last index
	 */
	private long				fLastIndexFileReadTimeMS;
	
	/**
	 * Number of ms taken to preprocess files during the last index
	 */
	private long				fLastIndexPreProcessTimeMS;
	
	/**
	 * Number of ms taken to parse files during the last index
	 */
	private long				fLastIndexParseTimeMS;
	
	/**
	 * Total number of ms taken during the last index
	 */
	private long				fLastIndexTotalTimeMS;
	
	
	public SVDBIndexStats() {
		
	}
	
	public int getNumRootFiles() {
		return fNumRootFiles;
	}
	
	public void setNumRootFiles(int n) {
		fNumRootFiles = n;
	}
	
	public int getNumTotalFiles() {
		return fNumTotalFiles;
	}
	
	public void setNumTotalFiles(int n) {
		fNumTotalFiles = n;
	}
	
	public int getNumProcessedFiles() {
		return fNumProcessedFiles;
	}
	
	public void setNumProcessedFiles(int n) {
		fNumProcessedFiles = n;
	}
	
	public void incNumProcessedFiles() {
		fNumProcessedFiles++;
	}
	
	public int getNumLines() {
		return fNumLines;
	}
	
	public void setNumLines(int n) {
		fNumLines = n;
	}
	
	public void incNumLines(int n) {
		fNumLines += n;
	}
	
	public long getLastIndexFileReadTime() {
		return fLastIndexFileReadTimeMS;
	}
	
	public void setLastIndexFileReadTime(long t) {
		fLastIndexFileReadTimeMS = t;
	}
	
	public void incLastIndexFileReadTime(long t) {
		fLastIndexFileReadTimeMS += t;
	}

	public long getLastIndexPreProcessTime() {
		return fLastIndexPreProcessTimeMS;
	}
	
	public void setLastIndexPreProcessTime(long t) {
		fLastIndexPreProcessTimeMS = t;
	}
	
	public void incLastIndexPreProcessTime(long t) {
		fLastIndexPreProcessTimeMS += t;
	}
	
	public long getLastIndexParseTime() {
		return fLastIndexParseTimeMS;
	}
	
	public void setLastIndexParseTime(long t) {
		fLastIndexParseTimeMS = t;
	}
	
	public void incLastIndexParseTime(long t) {
		fLastIndexParseTimeMS += t;
	}
	
	public long getLastIndexTotalTime() {
		return fLastIndexTotalTimeMS;
	}
	
	public void setLastIndexTotalTime(long t) {
		fLastIndexTotalTimeMS = t;
	}
	
	public void incLastIndexTotalTime(long t) {
		fLastIndexTotalTimeMS += t;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("* NumRootFiles: " + fNumRootFiles + "\n");
		sb.append("* NumProcessedFiles: " + fNumProcessedFiles + "\n");
		sb.append("* NumLines: " + fNumLines + "\n");
		sb.append("* FileReadTime: " + fLastIndexFileReadTimeMS + "\n");
		sb.append("* PreProcessTime: " + fLastIndexPreProcessTimeMS + "\n");
		sb.append("* ParseTime: " + fLastIndexParseTimeMS + "\n");
		sb.append("* TotalIndexTime: " + fLastIndexTotalTimeMS + "\n");
	
		return sb.toString();
	}
}
