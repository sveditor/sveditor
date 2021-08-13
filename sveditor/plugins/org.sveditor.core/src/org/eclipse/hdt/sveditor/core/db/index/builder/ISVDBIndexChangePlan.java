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
package org.sveditor.core.db.index.builder;

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
