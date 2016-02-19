package net.sf.sveditor.core.db.index.builder;

public interface ISVDBIndexBuilder {

	ISVDBIndexBuildJob build(ISVDBIndexChangePlan plan);

	ISVDBIndexBuildJob findJob(ISVDBIndexChangePlanner planner);
}
