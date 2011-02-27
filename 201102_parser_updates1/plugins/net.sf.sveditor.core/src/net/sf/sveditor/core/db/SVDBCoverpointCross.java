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

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.expr.SVExpr;
import net.sf.sveditor.core.db.persistence.DBFormatException;
import net.sf.sveditor.core.db.persistence.IDBReader;
import net.sf.sveditor.core.db.persistence.IDBWriter;
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBCoverpointCross extends SVDBScopeItem {
	private List<SVDBIdentifier>	fCoverpointList;
	private SVExpr					fIFF;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItemBase readSVDBItem(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
				return new SVDBCoverpointCross(parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.CoverCross); 
	}
	

	public SVDBCoverpointCross(String name) {
		super(name, SVDBItemType.CoverCross);
		fCoverpointList = new ArrayList<SVDBIdentifier>();
	}
	
	public SVExpr getIFF() {
		return fIFF;
	}
	
	public void setIFF(SVExpr expr) {
		fIFF = expr;
	}

	public List<SVDBIdentifier> getCoverpointList() {
		return fCoverpointList;
	}
	
	
	@SuppressWarnings("unchecked")
	public SVDBCoverpointCross(ISVDBChildItem parent, SVDBItemType type, IDBReader reader) 
		throws DBFormatException {
		super(parent, type, reader);

		fCoverpointList = (List<SVDBIdentifier>)reader.readItemList(this);
	}

	@Override
	public void dump(IDBWriter writer) {
		super.dump(writer);

		writer.writeItemList(fCoverpointList);
	}

	@Override
	public SVDBItemBase duplicate() {
		SVDBCoverpointCross ret = new SVDBCoverpointCross(getName());
		
		ret.init(this);
		
		return ret;
	}

	@Override
	public void init(SVDBItemBase other) {
		SVDBCoverpointCross other_i = (SVDBCoverpointCross)other;
		
		super.init(other);
		
		fCoverpointList.clear();
		fCoverpointList.addAll(other_i.fCoverpointList);
	}


	@Override
	public boolean equals(Object obj) {
		if (obj instanceof SVDBCoverpointCross) {
			SVDBCoverpointCross o = (SVDBCoverpointCross)obj;
			if (o.fCoverpointList.size() == fCoverpointList.size()) {
				for (int i=0; i<fCoverpointList.size(); i++) {
					if (!o.fCoverpointList.get(i).equals(fCoverpointList.get(i))) {
						return false;
					}
				}
			}
			return super.equals(obj);
		}
		
		return false;
	}

}
