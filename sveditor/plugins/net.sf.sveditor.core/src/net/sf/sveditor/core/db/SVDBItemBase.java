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

import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;



public abstract class SVDBItemBase implements ISVDBItemBase {
	
	@SVDBDoNotSaveAttr
	public SVDBItemType			fType;
	
	public long					fLocation;
	
	protected SVDBItemBase(SVDBItemType type) {
		fType = type;
		fLocation = -1;
	}
	
	public SVDBItemType getType() {
		return fType;
	}
	
	public void setType(SVDBItemType type) {
		fType = type;
	}

	public long getLocation() {
		return fLocation;
	}

	public void setLocation(long location) {
		fLocation = location;
	}

	public ISVDBItemBase duplicate() {
		return SVDBItemUtils.duplicate(this);
	}

	public void init(ISVDBItemBase other) {
		// Treat fType as immutable: fType = other.getType();
		fLocation = other.getLocation();
	}
	
	public boolean equals(Object obj) {
		if (obj instanceof SVDBItemBase) {
			SVDBItemBase o = (SVDBItemBase)obj;
			return (o.fType == fType);
		} else {
			return false;
		}
	}

	public boolean equals(ISVDBItemBase obj, boolean full) {
		boolean ret = false;
		if (obj instanceof SVDBItemBase) {
			ret = true;
			SVDBItemBase other = (SVDBItemBase)obj;

			if (other.fType == null || fType == null) {
				ret &= other.fType == fType;
			} else {
				ret &= other.fType.equals(fType);
			}

			if (full) {
				ret &= (fLocation == other.fLocation);
			}
		}
		
		return ret;
	}

	@Override
	public void accept(ISVDBVisitor v) {
		System.out.println("WARN: accept method not implemented for " + getClass());
	}
	
}
