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
