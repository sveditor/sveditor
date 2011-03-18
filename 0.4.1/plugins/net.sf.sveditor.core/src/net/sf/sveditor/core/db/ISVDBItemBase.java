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

import net.sf.sveditor.core.db.persistence.IDBWriter;

public interface ISVDBItemBase {
	
	SVDBItemType getType();
	
	SVDBLocation getLocation();
	
	void setLocation(SVDBLocation location);
	
	void dump(IDBWriter writer);
	
	ISVDBItemBase duplicate();
	
	void init(ISVDBItemBase other);
	
	boolean equals(ISVDBItemBase other, boolean recurse);

}
