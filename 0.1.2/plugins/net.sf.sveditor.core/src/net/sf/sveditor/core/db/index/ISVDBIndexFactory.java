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


public interface ISVDBIndexFactory {
	
	/*
	String TYPE_WorkspaceIndex  = "net.sf.sveditor.workspaceIndex";
	String TYPE_FilesystemIndex = "net.sf.sveditor.fileSystemIndex";
	String TYPE_PluginLibIndex  = "net.sf.sveditor.pluginLibIndex";
	// String TYPE_PackageLibIndex = "net.sf.sveditor.packageLibIndex";
	 */
	
	
	ISVDBIndex createSVDBIndex(
			String 					project_name, 
			String 					base_location,
			Map<String, Object>		config);

}
