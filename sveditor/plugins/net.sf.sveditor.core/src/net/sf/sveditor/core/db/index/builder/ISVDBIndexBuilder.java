package net.sf.sveditor.core.db.index.builder;

public interface ISVDBIndexBuilder {

	SVDBIndexBuildJob build(ISVDBIndexChangePlan plan);

	SVDBIndexBuildJob findJob(ISVDBIndexChangePlanner planner);
}
