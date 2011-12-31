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


package net.sf.sveditor.core.db.index;

import java.util.ArrayList;
import java.util.List;

public class SVDBArgFileIndexCacheData extends SVDBBaseIndexCacheData {
	
	private List<String>			fArgFilePaths;
	private List<Long>				fArgFileTimestamps;
	
	public SVDBArgFileIndexCacheData(String base_location) {
		super(base_location);
		fArgFileTimestamps = new ArrayList<Long>();
		fArgFilePaths = new ArrayList<String>();
	}
	
	public List<Long> getArgFileTimestamps() {
		return fArgFileTimestamps;
	}
	
	public List<String> getArgFilePaths() {
		return fArgFilePaths;
	}
	
}
