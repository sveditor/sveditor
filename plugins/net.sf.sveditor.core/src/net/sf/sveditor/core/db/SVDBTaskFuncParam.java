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
import net.sf.sveditor.core.db.persistence.ISVDBPersistenceFactory;
import net.sf.sveditor.core.db.persistence.SVDBPersistenceReader;

public class SVDBTaskFuncParam extends SVDBVarDeclItem {
	public static final int			Direction_Input  = (1 << 16);
	public static final int			Direction_Output = (1 << 17);
	public static final int			Direction_Inout  = (1 << 18);
	public static final int			Direction_Ref    = (1 << 19);
	public static final int			Direction_Const  = (1 << 20);
	public static final int			Direction_Var    = (1 << 21);
	private int						fDir;
	
	public static void init() {
		ISVDBPersistenceFactory f = new ISVDBPersistenceFactory() {
			public SVDBItem readSVDBItem(IDBReader reader, SVDBItemType type, 
					SVDBFile file, SVDBScopeItem parent) throws DBFormatException {
				return new SVDBTaskFuncParam(file, parent, type, reader);
			}
		};
		
		SVDBPersistenceReader.registerPersistenceFactory(f, SVDBItemType.TaskFuncParam); 
	}
	
	public SVDBTaskFuncParam(SVDBTypeInfo type, String name) {
		super(type, name, SVDBItemType.TaskFuncParam);
		fDir = Direction_Input;
	}
	
	public void setDir(int dir) {
		fDir = dir;
	}
	
	public int getDir() {
		return fDir;
	}
	
	public SVDBItem duplicate() {
		SVDBItem ret = new SVDBTaskFuncParam(fTypeInfo, getName());
		
		init(ret);
		
		return ret;
	}
	
	public void init(SVDBItem other) {
		super.init(other);
		
		fDir = ((SVDBTaskFuncParam)other).fDir; 
	}
	
	public SVDBTaskFuncParam(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		
		fDir = reader.readInt();
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		writer.writeInt(fDir);
	}
	
	
}
