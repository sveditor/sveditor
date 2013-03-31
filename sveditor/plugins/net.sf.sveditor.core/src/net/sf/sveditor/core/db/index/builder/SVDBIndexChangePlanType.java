package net.sf.sveditor.core.db.index.builder;

public enum SVDBIndexChangePlanType {
	/**
	 * An empty plan indicates no need to do any work
	 */
	Empty,

	/**
	 * Requests a refresh operation on the index. This 
	 * may result in a new plan being computed
	 */
	Refresh,
	
	/**
	 * Requests rebuild of specific files. 
	 */
	RebuildFile,
	
	/**
	 * Requests rebuild of the full index
	 */
	RebuildIndex,
	
	/**
	 * Composite plan involving multiple indexes
	 */
	Composite

}
