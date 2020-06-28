/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
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
	 * Number of ms taken to index declarations from files
	 */
	private long				fLastIndexDeclIndexTimeMS;
	
	/**
	 * Number of ms taken to index references
	 */
	private long				fLastIndexRefIndexTimeMS;
	
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
	
	public long getLastIndexDeclCacheTime() {
		return fLastIndexDeclIndexTimeMS;
	}
	
	public void incLastIndexDeclCacheTime(long t) {
		fLastIndexDeclIndexTimeMS += t;
	}
	
	public long getLastIndexRefCacheTime() {
		return fLastIndexRefIndexTimeMS;
	}
	
	public void incLastIndexRefCacheTime(long t) {
		fLastIndexRefIndexTimeMS += t;
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
		sb.append("*\n");
		
		sb.append("* PreProcess Lines/s: " + calcNPerS(fNumLines, fLastIndexPreProcessTimeMS) + "\n");
		sb.append("* Parse Lines/s: " + calcNPerS(fNumLines, fLastIndexParseTimeMS) + "\n");
		sb.append("* Index Lines/s: " + calcNPerS(fNumLines, fLastIndexTotalTimeMS) + "\n");
	
		return sb.toString();
	}
	
	public void add(SVDBIndexStats other) {
		fNumRootFiles += other.fNumRootFiles;
		fNumProcessedFiles += other.fNumProcessedFiles;
		fNumLines += other.fNumLines;
		fLastIndexFileReadTimeMS += other.fLastIndexDeclIndexTimeMS;
		fLastIndexPreProcessTimeMS += other.fLastIndexPreProcessTimeMS;
		fLastIndexDeclIndexTimeMS += other.fLastIndexDeclIndexTimeMS;
		fLastIndexRefIndexTimeMS += other.fLastIndexRefIndexTimeMS;
		fLastIndexParseTimeMS += other.fLastIndexParseTimeMS;
		fLastIndexTotalTimeMS += other.fLastIndexTotalTimeMS;
	}
	
	public static long calcNPerS(int n, long ms) {
		long n_tmp = n;
		long t_tmp = ms;
		
		if (t_tmp <= 0) {
			return -1;
		}
		
		n_tmp *= 1000;
		n_tmp /= t_tmp;
		
		return n_tmp;
	}
}
