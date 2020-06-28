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
package org.eclipse.hdt.sveditor.core.db.index.builder;

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
