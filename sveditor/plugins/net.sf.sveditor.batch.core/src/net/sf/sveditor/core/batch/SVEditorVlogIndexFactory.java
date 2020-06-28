/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.batch;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.SVDBIndexUtil;
import net.sf.sveditor.core.db.index.argfile.SVDBArgFileIndexFactory;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;

import org.eclipse.core.runtime.NullProgressMonitor;

public class SVEditorVlogIndexFactory {

	public static ISVDBIndex vlog(String args[]) {
		return vlog_loc(System.getProperty("user.dir"), args);
	}
	
	public static ISVDBIndex vlog_loc(String location, String args[]) {
		ISVDBIndex index = null;
		
		SVDBArgFileIndexFactory f = new SVDBArgFileIndexFactory();
		
		// Select a temporary directory
		File tmpdir = SVBatchPlugin.createTempDir();
		File db = new File(tmpdir, "db");
		ISVDBIndexCacheMgr cache_mgr = SVCorePlugin.createCacheMgr(db);

		PrintStream ps = null;
		
		try {
			ps = new PrintStream(new File(tmpdir, "args.f"));

			for (String arg : args) {
				arg = SVDBIndexUtil.expandVars(arg, null, false);
				if (arg.indexOf(' ') != -1 || arg.indexOf('\t') != -1) {
					ps.println("\"" + arg + "\"");
				} else {
					ps.println(arg);
				}
			}
			ps.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		
		String project = "GLOBAL";
		String base_location = new File(tmpdir, "args.f").getAbsolutePath();

		index = f.createSVDBIndex(
				project,
				base_location,
				cache_mgr.createIndexCache(project, base_location),
				null);
		
		index.init(new NullProgressMonitor(), null);
		
		SVBatchPlugin.addIndex(index);
		
		return index;
	}
	/*
	 */

}
