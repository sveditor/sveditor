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

public class SVDBInitialBlock extends SVDBScopeItem {
	
	public SVDBInitialBlock() {
		super("", SVDBItemType.InitialBlock);
	}

	public SVDBInitialBlock(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
	}

	@Override
	public SVDBItem duplicate() {
		SVDBInitialBlock ret = new SVDBInitialBlock();
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItem other) {
		super.init(other);
	}

}
