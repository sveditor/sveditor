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


package net.sf.sveditor.core.db.index.old;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexFactory;
import net.sf.sveditor.core.db.index.SVDBFSFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBIndexConfig;
import net.sf.sveditor.core.db.index.SVDBWSFileSystemProvider;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.db.project.SVDBSourceCollection;
import net.sf.sveditor.core.fileset.AbstractSVFileMatcher;
import net.sf.sveditor.core.fileset.SVFileSet;
import net.sf.sveditor.core.fileset.SVFilesystemFileMatcher;
import net.sf.sveditor.core.fileset.SVWorkspaceFileMatcher;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.log.LogHandle;

public class SVDBSourceCollectionIndexFactory implements ISVDBIndexFactory {
	
	public static final String	TYPE = "net.sf.sveditor.sourceCollectionIndex";
	
	// 
	public static final String  	FILESET = "FILE_SET";
	private LogHandle				fLog;
	
	public SVDBSourceCollectionIndexFactory() {
		fLog = LogFactory.getLogHandle("SVDBSourceCollectionIndexFactory");
	}
	

	public ISVDBIndex createSVDBIndex(
			String 					project_name,
			String 					base_location,
			ISVDBIndexCache			cache,
			SVDBIndexConfig			config) {
		ISVDBIndex ret;
		ISVDBFileSystemProvider fs_provider = null;
		List<AbstractSVFileMatcher> matcher_list = new ArrayList<AbstractSVFileMatcher>();
		
		fLog.debug("createSVDBIndex: " + project_name + " ; " + base_location);
		
		SVFileSet fs = null;
		AbstractSVFileMatcher matcher = null;
		
		if (config != null) {
			fs = (SVFileSet)config.get(FILESET);
		}
		
		if (base_location.startsWith("${workspace_loc}")) {
			
			if (fs == null) {
				// Create a default fileset
				fs = new SVFileSet(base_location);
				fs.getIncludes().addAll(SVDBSourceCollection.parsePatternList(
						SVCorePlugin.getDefault().getDefaultSourceCollectionIncludes()));
				fs.getExcludes().addAll(SVDBSourceCollection.parsePatternList(
						SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes()));
			}
			
			matcher = new SVWorkspaceFileMatcher();
			matcher.addFileSet(fs);
			
			fs_provider = new SVDBWSFileSystemProvider();
			matcher_list.add(matcher);
			
		} else {
			if (fs == null) {
				// Create a default fileset
				fs = new SVFileSet(base_location);
				fs.getIncludes().addAll(SVDBSourceCollection.parsePatternList(
						SVCorePlugin.getDefault().getDefaultSourceCollectionIncludes()));
				fs.getExcludes().addAll(SVDBSourceCollection.parsePatternList(
						SVCorePlugin.getDefault().getDefaultSourceCollectionExcludes()));
			}
			
			matcher = new SVFilesystemFileMatcher();
			matcher.addFileSet(fs);
			
			fs_provider = new SVDBFSFileSystemProvider();
			matcher_list.add(matcher);
		}

		ret = new SVDBSourceCollectionIndex(project_name, base_location, 
				matcher_list, fs_provider, cache, config);
		
		return ret;
	}
}