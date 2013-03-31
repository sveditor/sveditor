package net.sf.sveditor.core.db.index.builder;

public interface ISVDBIndexChangePlan {

	/**
	 * Indicates whether these two plans can be merged
	 * 
	 * @param other
	 * @return
	 */
	boolean canMerge(ISVDBIndexChangePlan other);
	
	/**
	 * Merge 'other' plan with this one, resulting in a
	 * new plan
	 * 
	 * @param other
	 * @return
	 */
	ISVDBIndexChangePlan merge(ISVDBIndexChangePlan other);
	
	ISVDBIndexChangePlanner getPlanner();
	
	SVDBIndexChangePlanType getType();

}
