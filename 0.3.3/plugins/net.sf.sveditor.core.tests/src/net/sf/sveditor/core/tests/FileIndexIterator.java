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


package net.sf.sveditor.core.tests;

import java.util.HashMap;
import java.util.Map;

import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.db.index.SVDBIndexItemIterator;

public class FileIndexIterator implements ISVDBIndexIterator {
	Map<String, SVDBFile>			fFileMap;
	
	public FileIndexIterator(SVDBFile file) {
		fFileMap = new HashMap<String, SVDBFile>();
		fFileMap.put(file.getName(), file);
	}

	public ISVDBItemIterator<SVDBItem> getItemIterator() {
		return new SVDBIndexItemIterator(fFileMap);
	}

}
