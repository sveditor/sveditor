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
package net.sf.sveditor.core.db.refs;


public abstract class SVDBRefSearchSpecByNameBase implements ISVDBRefSearchSpec {
	protected String					fName;
	protected NameMatchType			fMatchType;
	
	protected SVDBRefSearchSpecByNameBase(
			String 			name, 
			NameMatchType 	type) {
		fName = name;
		fMatchType = type;
	}
	
	@Override
	public NameMatchType getNameMatchType() {
		return fMatchType;
	}

	@Override
	public String getName() {
		return fName;
	}

}
