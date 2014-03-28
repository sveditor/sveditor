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


package net.sf.sveditor.core.fileset;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.log.LogFactory;

public class SVFilesystemFileMatcher extends AbstractSVFileMatcher {
	
	public SVFilesystemFileMatcher() {
		fLog = LogFactory.getLogHandle("SVFilesystemFileMatcher");
	}

	@Override
	public List<String> findIncludedPaths() {
		List<String> ret = new ArrayList<String>();
		
		for (SVFileSet fs : fFileSets) {
			File base = new File(fs.getBase());
			
			findIncludedPaths(fs.getBase(), ret, base);
		}
		
		return ret;
	}
	
	private void findIncludedPaths(String base, List<String> paths, File parent) {
		if (parent.isFile()) {
			if (include_file(parent.getAbsolutePath())) {
				if (!paths.contains(parent.getAbsolutePath())) {
					paths.add(parent.getAbsolutePath());
				}
			}
		} else if (parent.isDirectory()) {
			File file_list[] = parent.listFiles();
		
			if (file_list != null) {
				for (File file : file_list) {
					if (file.isDirectory()) {
						if (include_dir(file.getAbsolutePath())) {
							findIncludedPaths(base, paths, file);
						}
					} else {
						if (include_file(file.getAbsolutePath())) {
							if (!paths.contains(file.getAbsolutePath())) {
								paths.add(file.getAbsolutePath());
							}
						}
					}
				}
			}
		} else {
			fLog.error("Base path \"" + parent.getAbsolutePath() + "\" does not exist");
		}
	}
}
