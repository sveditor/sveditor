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

import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;

public class SVDBCoverPoint extends SVDBItem {
	private String				fTarget;
	private String				fBody;
	
	public SVDBCoverPoint(String name, String target, String body) {
		super(name, SVDBItemType.Coverpoint);
		fTarget = target;
		fBody = body;
	}
	
	public String getTarget() {
		return fTarget;
	}
	
	public String getBody() {
		return fBody;
	}
	
	public SVDBCoverPoint(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) 
		throws DBFormatException {
		super(file, parent, type, reader);
		
		fTarget = reader.readString();
		fBody = reader.readString();
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);
		
		writer.writeString(fTarget);
		writer.writeString(fBody);
	}

	@Override
	public SVDBItem duplicate() {
		SVDBCoverPoint ret = new SVDBCoverPoint(getName(), fTarget, fBody);
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItem other) {
		SVDBCoverPoint other_i = (SVDBCoverPoint)other;
		
		super.init(other);
		
		fTarget = other_i.fTarget;
	}
	
}
