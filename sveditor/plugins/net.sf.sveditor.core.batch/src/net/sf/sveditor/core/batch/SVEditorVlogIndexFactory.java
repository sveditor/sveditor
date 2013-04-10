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


package net.sf.sveditor.core.batch;

public class SVEditorVlogIndexFactory {

	/*
	public static ISVDBIndex vlog(String args[]) {
		return vlog_loc(System.getProperty("user.dir"), args);
	}
	
	public static ISVDBIndex vlog_loc(String location, String args[]) {
		ISVDBIndex index = null;
		StringBuilder sb = new StringBuilder();
		
		for (String arg : args) {
			arg = SVDBIndexUtil.expandVars(arg, null, false);
			if (arg.indexOf(' ') != -1 || arg.indexOf('\t') != -1) {
				sb.append("\"" + arg + "\"\n");
			} else {
				sb.append(arg + "\n");
			}
		}
		
		SVDBArgFileIndexFactory f = new SVDBArgFileIndexFactory();
		
		// Select a temporary directory
		File tmpdir = SVBatchPlugin.createTempDir();
		SVDBDirFS dir_fs = new SVDBDirFS(tmpdir);
		SVDBFileIndexCache index_c = new SVDBFileIndexCache(dir_fs);
		
		index = f.createSVDBIndex(null, location, sb, index_c, null);
		
		index.init(new NullProgressMonitor());
		
		return index;
	}
	 */

}
