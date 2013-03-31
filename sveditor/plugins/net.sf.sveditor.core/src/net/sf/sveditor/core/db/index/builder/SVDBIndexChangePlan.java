package net.sf.sveditor.core.db.index.builder;

/**
 * @author ballance
 *
 */
public class SVDBIndexChangePlan implements ISVDBIndexChangePlan {
	protected SVDBIndexChangePlanType			fType;
	protected ISVDBIndexChangePlanner			fPlanner;
	
	public SVDBIndexChangePlan(ISVDBIndexChangePlanner planner, SVDBIndexChangePlanType type) {
		fPlanner = planner;
		fType = type;
	}

	public boolean canMerge(ISVDBIndexChangePlan other) {
		return false;
	}

	public ISVDBIndexChangePlan merge(ISVDBIndexChangePlan other) {
		// TODO Auto-generated method stub
		return null;
	}

	public ISVDBIndexChangePlanner getPlanner() {
		return fPlanner;
	}

	public SVDBIndexChangePlanType getType() {
		return fType;
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBIndexChangePlan) {
			SVDBIndexChangePlan other = (SVDBIndexChangePlan)obj;
			boolean ret = true;
			
			ret &= (fType.equals(other.fType));
			
			ret &= (fPlanner == other.fPlanner);
			
			return ret;
		} else {
			return false;
		}
	}

	
}
