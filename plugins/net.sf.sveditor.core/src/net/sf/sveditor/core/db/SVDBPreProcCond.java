/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db;



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
