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

import org.sveditor.core.db.attr.SVDBDoNotSaveAttr;



public class SVDBItemBase implements ISVDBItemBase {
	
	@SVDBDoNotSaveAttr
	public SVDBItemType			fType;
	
	public long					fLocation;
	
	public SVDBItemBase(SVDBItemType type) {
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
	
}
