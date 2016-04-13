package net.sf.sveditor.core.db.index.builder;

public interface ISVDBIndexBuildJob {
	
	ISVDBIndexChangePlan getPlan();
	
	void waitComplete();
	
	boolean canReplace(ISVDBIndexChangePlan plan);

}
