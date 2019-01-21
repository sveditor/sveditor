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

import java.io.File;

import net.sf.sveditor.core.db.attr.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.index.ISVDBIndex;

public class SVDBFile extends SVDBScopeItem {
	@SVDBDoNotSaveAttr
	public ISVDBIndex					fIndex;
	public String						fFile;
	
	public SVDBFile() {
		super("", SVDBItemType.File);
		fFile = "";
	}
	
	public SVDBFile(String file) {
		this(file, SVDBItemType.File);
	}
	
	protected SVDBFile(String file, SVDBItemType type) {
		super(file, type);
		
		if (file != null) {
			setName(new File(file).getName());
		}
		fFile               = file;
		setLocation(-1);		
	}
	
	public void setIndex(ISVDBIndex index) {
		fIndex = index;
	}
	
	public ISVDBIndex getIndex() {
		return fIndex;
	}

	public String getFilePath() {
		return fFile;
	}
	
	public void clearChildren() {
		fItems.clear();
	}

	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_file(this);
	}
	
	
}
