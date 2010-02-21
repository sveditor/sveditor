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


package net.sf.sveditor.core.db.index;

import java.util.Map;

public class SVDBArgFileIndexFactory implements ISVDBIndexFactory {
	
	public static final String	TYPE = "net.sf.sveditor.argFileIndex";

	public ISVDBIndex createSVDBIndex(
			String 					projectName, 
			String 					base_location,
			Map<String, Object> 	config) {
		ISVDBFileSystemProvider fs_provider;
		
		if (base_location.startsWith("${workspace_loc}")) {
			fs_provider = new SVDBWSFileSystemProvider();
		} else {
			fs_provider = new SVDBFSFileSystemProvider();
		}

		SVDBArgFileIndex index = new SVDBArgFileIndex(
				projectName, base_location, fs_provider);
		

		SVDBIndexFactoryUtils.setBaseProperties(config, index);
		
		return index;
	}

}
