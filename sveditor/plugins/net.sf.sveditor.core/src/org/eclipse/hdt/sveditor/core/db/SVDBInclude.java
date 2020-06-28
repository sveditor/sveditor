/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package org.eclipse.hdt.sveditor.core.db;


public class SVDBInclude extends SVDBItem {
	
	public SVDBInclude() {
		super("", SVDBItemType.Include);
	}
	
	public SVDBInclude(String name) {
		super(name, SVDBItemType.Include);
	}
	
	@Override
	public SVDBInclude duplicate() {
		return (SVDBInclude)super.duplicate();
	}

	@Override
	public void init(SVDBItemBase other) {
		super.init(other);
	}
	

}
