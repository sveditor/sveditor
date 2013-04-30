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

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileIndexCacheMgr;
import net.sf.sveditor.core.db.index.cache.file.SVDBFileSystem;

import org.osgi.framework.BundleActivator;
import org.osgi.framework.BundleContext;

public class SVBatchPlugin implements BundleActivator {

	private static BundleContext 	context;
	private static SVBatchPlugin	fDefault;
	private List<File>				fTempDirs;
	private List<ISVDBIndex>		fLocalIndexes;
	private SVDBFileSystem			fFileSystem;
	private SVDBFileIndexCacheMgr	fCacheMgr;

	static BundleContext getContext() {
		return context;
	}
	
	static SVBatchPlugin getDefault() {
		return fDefault;
	}

	/*
	 * (non-Javadoc)
	 * @see org.osgi.framework.BundleActivator#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext bundleContext) throws Exception {
		SVBatchPlugin.context = bundleContext;
		fTempDirs = new ArrayList<File>();
		fLocalIndexes = new ArrayList<ISVDBIndex>();
		fDefault = this;
		
		File db_dir = createTempDir();
		fFileSystem = new SVDBFileSystem(db_dir, SVCorePlugin.getVersion());
		fFileSystem.init();
		fCacheMgr = new SVDBFileIndexCacheMgr();
		fCacheMgr.init(fFileSystem);
	}

	/*
	 * (non-Javadoc)
	 * @see org.osgi.framework.BundleActivator#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext bundleContext) throws Exception {
		for (ISVDBIndex index : fLocalIndexes) {
			index.dispose();
		}
		for (File tmpdir : fTempDirs) {
			deleteTree(tmpdir);
		}
		
		SVBatchPlugin.context = null;
		fDefault = null;
	}
	
	public ISVDBIndexCacheMgr getCacheMgr() {
		return fCacheMgr;
	}
	
	private static void deleteTree(File dir) {
		if (dir.isFile()) {
			dir.delete();
		} else {
			File e[] = dir.listFiles();
			if (e != null) {
				for (File t : e) {
					if (t.getName().equals(".") || t.getName().equals("..")) {
						System.out.println("ERROR");
						continue;
					}
					if (t.isDirectory()) {
						deleteTree(t);
					} else {
						t.delete();
					}
				}
			}
			dir.delete();
		}
	}

	public static synchronized File createTempDir() {
		File tmpdir = new File(System.getProperty("java.io.tmpdir"));
		File ret = null; 
		
		for (int i=1; i<10000; i++) {
			File tmp = new File(tmpdir, "sveditor_tmp_" + i);
			if (!tmp.isDirectory()) {
				tmp.mkdirs();
				ret = tmp;
				break;
			}
		}
		
		if (ret != null) {
			fDefault.fTempDirs.add(ret);
		} else {
			System.out.println("Failed to create temp dir");
		}
		
		return ret;
	}
	
	public static synchronized void addIndex(ISVDBIndex index) {
		fDefault.fLocalIndexes.add(index);
	}
}
