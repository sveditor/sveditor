/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db;


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
