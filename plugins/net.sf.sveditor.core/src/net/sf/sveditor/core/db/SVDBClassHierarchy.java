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

/**
 * The class hierarchy object represents an expanded class hierarchy
 * 
 * @author ballance
 *
 */
public class SVDBClassHierarchy extends SVDBModIfcClassDecl {
	
	private SVDBModIfcClassDecl					fOrigClass;
	private SVDBClassHierarchy					fParentClass;
	
	public SVDBClassHierarchy(SVDBModIfcClassDecl orig_class) {
		super(orig_class.getName(), SVDBItemType.Class);
		
		fOrigClass = orig_class;
		super.init(fOrigClass);
	}
	
	public SVDBClassHierarchy(SVDBFile file, SVDBScopeItem parent, SVDBItemType type, IDBReader reader) throws DBFormatException {
		super(file, parent, type, reader);
		System.out.println("[ERROR] trying to load SVDBClassHierarchy");
	}
	
	public void dump(IDBWriter writer) {
		super.dump(writer);
		System.out.println("[ERROR] trying to dump SVDBClassHierarchy");
	}
	
	
	public SVDBClassHierarchy getParentClass() {
		return fParentClass;
	}
	
	public void setParentClass(SVDBClassHierarchy parent) {
		fParentClass = parent;
	}
	
}
