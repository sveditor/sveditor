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


package org.sveditor.core.db;



public class SVDBPreProcCond extends SVDBScopeItem {
	public String						fConditional;
	
	public SVDBPreProcCond() {
		super("", SVDBItemType.PreProcCond);
	}
	
	public SVDBPreProcCond(String name, String conditional) {
		super(name, SVDBItemType.PreProcCond);
		fConditional = conditional;
	}
	
	public String getConditional() {
		return fConditional;
	}
	
	public void init(SVDBItemBase other) {
		super.init(other);
	}
	
	public boolean equals(Object obj) {
		if (super.equals(obj) && obj instanceof SVDBPreProcCond) {
			return fConditional.equals(((SVDBPreProcCond)obj).fConditional) &&
				super.equals(obj);
		}
		return false;
	}
}
