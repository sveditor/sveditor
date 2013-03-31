package net.sf.sveditor.core.db.index.builder;

public class SVDBIndexChangePlanRebuild extends SVDBIndexChangePlan {
	
	public SVDBIndexChangePlanRebuild(ISVDBIndexChangePlanner planner) {
		super(planner, SVDBIndexChangePlanType.RebuildIndex);
	}

}
