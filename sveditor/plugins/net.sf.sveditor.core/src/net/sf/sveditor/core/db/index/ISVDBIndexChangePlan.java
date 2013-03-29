package net.sf.sveditor.core.db.index;

public interface ISVDBIndexChangePlan {
	
	/**
	 * Merge 'other' plan with this one, resulting in a
	 * new plan
	 * 
	 * @param other
	 * @return
	 */
	ISVDBIndexChangePlan merge(ISVDBIndexChangePlan other);
	
	ISVDBIndexChangePlanner getPlanner();

}
