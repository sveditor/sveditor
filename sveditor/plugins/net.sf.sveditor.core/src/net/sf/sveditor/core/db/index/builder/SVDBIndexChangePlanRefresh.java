package net.sf.sveditor.core.db.index.builder;

public class SVDBIndexChangePlanRefresh extends SVDBIndexChangePlan {
	
	public SVDBIndexChangePlanRefresh(ISVDBIndexChangePlanner planner) {
		super(planner, SVDBIndexChangePlanType.Refresh);
	}

	@Override
	public boolean canMerge(ISVDBIndexChangePlan other) {
		return (merge(other) != null);
	}

	@Override
	public ISVDBIndexChangePlan merge(ISVDBIndexChangePlan other) {
		// We can merge if the 'other' plan supersedes 
		// or is identical to this one 

		if (other.getPlanner() == getPlanner()) {
			if (other.getType() == SVDBIndexChangePlanType.RebuildIndex) {
				// Supersedes our refresh plan
				return other;
			} else if (other.getType() == SVDBIndexChangePlanType.Refresh) {
				// Equals
				return other;
			}
		}
		return null;
	}

}
