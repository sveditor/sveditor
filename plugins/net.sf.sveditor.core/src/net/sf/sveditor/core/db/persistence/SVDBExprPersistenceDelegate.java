/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.persistence;

import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItemType;

public class SVDBExprPersistenceDelegate extends SVDBPersistenceRWDelegateBase {

	public void writeObject(Class cls, Object obj) throws DBWriteException {
		// TODO Auto-generated method stub

	}

	public void writeSVDBItem(ISVDBItemBase item) throws DBWriteException {
		// TODO Auto-generated method stub

	}

	public void writeEnumType(Class cls, Enum value) throws DBWriteException {
		// TODO Auto-generated method stub

	}

	public void readObject(ISVDBChildItem parent, Class cls, Object obj)
			throws DBFormatException {
		// TODO Auto-generated method stub

	}

	public ISVDBItemBase readSVDBItem(SVDBItemType type, ISVDBChildItem parent)
			throws DBFormatException {
		// TODO Auto-generated method stub
		return null;
	}

	public Enum readEnumType(Class enum_type) throws DBFormatException {
		// TODO Auto-generated method stub
		return null;
	}

}
