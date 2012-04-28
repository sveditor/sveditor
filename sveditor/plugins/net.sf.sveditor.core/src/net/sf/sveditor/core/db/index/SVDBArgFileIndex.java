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

import java.io.InputStream;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.InputStreamTextScanner;
import net.sf.sveditor.core.svf_scanner.SVFScanner;

import org.apache.tools.ant.filters.StringInputStream;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;

public class SVDBArgFileIndex extends AbstractSVDBIndex {
	private StringBuilder				fArguments;
	
	public SVDBArgFileIndex(
			String						project,
			String						root,
			ISVDBFileSystemProvider		fs_provider,
			ISVDBIndexCache				cache,
			Map<String, Object>			config) {
		super(project, root, fs_provider, cache, config);
		fInWorkspaceOk = (root.startsWith("${workspace_loc}"));
	}

	public SVDBArgFileIndex(
			String						project,
			String						root,
			StringBuilder				arguments,
			ISVDBFileSystemProvider		fs_provider,
			ISVDBIndexCache				cache,
			Map<String, Object>			config) {
		super(project, root, fs_provider, cache, config);
		fArguments = arguments;
		fInWorkspaceOk = (root.startsWith("${workspace_loc}"));
	}
	
	@Override
	protected String getLogName() {
		return "SVDBArgFileIndex";
	}

	public String getTypeID() {
		return SVDBArgFileIndexFactory.TYPE;
	}
	
	@Override
	protected SVDBBaseIndexCacheData createIndexCacheData() {
		return new SVDBArgFileIndexCacheData(getBaseLocation());
	}
	
	@Override
	protected boolean checkCacheValid() {
		SVDBArgFileIndexCacheData cd = (SVDBArgFileIndexCacheData)getCacheData();

		int i=0;
		for (String arg_file : cd.getArgFilePaths()) {
			long ts = getFileSystemProvider().getLastModifiedTime(arg_file);
			long ts_c = cd.getArgFileTimestamps().get(i);
			if (ts > ts_c) {
				fLog.debug("    arg_file " + arg_file + " ts=" + ts + " cached ts=" + ts_c);
				return false;
			}
			i++;
		}

		return super.checkCacheValid();
	}

	@Override
	protected void discoverRootFiles(IProgressMonitor monitor) {
		fLog.debug("discoverRootFiles - " + getBaseLocation());
		
		clearFilesList();
		clearIncludePaths();
		clearDefines();
		
		monitor.beginTask("Discover Root Files", 4);
		
		SVDBArgFileIndexCacheData cd = (SVDBArgFileIndexCacheData)getCacheData();
		cd.getArgFileTimestamps().clear();
		cd.getArgFilePaths().clear();
		
		// Add an include path for the arg file location
		addIncludePath(getResolvedBaseLocationDir());
		
		processArgFile(new SubProgressMonitor(monitor, 4), getResolvedBaseLocation());
		
		monitor.done();
	}
	
	private void processArgFile(IProgressMonitor monitor, String path) {
		InputStream in = null;
		if (fArguments != null) {
			in = new StringInputStream(fArguments.toString());
		} else if (getFileSystemProvider().fileExists(path)) {
			// Fully-specified path
			in = getFileSystemProvider().openStream(path);
		} else if (getFileSystemProvider().fileExists(getResolvedBaseLocationDir() + "/" + path)) {
			// Try base location-relative
			in = getFileSystemProvider().openStream(getResolvedBaseLocationDir() + "/" + path);
		}
		
		monitor.beginTask("Process arg file " + path, 4);
		
		if (in != null) {
			SVDBArgFileIndexCacheData cd = (SVDBArgFileIndexCacheData)getCacheData();
			cd.getArgFilePaths().add(path);
			cd.getArgFileTimestamps().add(getFileSystemProvider().getLastModifiedTime(path));
			
			ITextScanner sc = new InputStreamTextScanner(in, path);
			SVFScanner scanner = new SVFScanner();
		
			monitor.worked(1);
			try {
				scanner.scan(sc);
			} catch (Exception e) {
				fLog.error("Failed to read argument file \"" + 
						getResolvedBaseLocation() + "\"", e);
			}
			
			monitor.worked(1);
			for (String f : scanner.getFilePaths()) {
				String exp_f = SVDBIndexUtil.expandVars(f, fProjectName, fInWorkspaceOk);
				fLog.debug("[FILE PATH] " + f + " (" + exp_f + ")");
				String res_f = resolvePath(exp_f, fInWorkspaceOk);
				
				if (getFileSystemProvider().fileExists(res_f)) {
					addFile(res_f);
				} else {
					fLog.error("Expanded path \"" + exp_f + "\" does not exist");
				}
			}
			
			for (String lib_p : scanner.getLibPaths()) {
				String exp_p = SVDBIndexUtil.expandVars(lib_p, fProjectName, fInWorkspaceOk);
				fLog.debug("[LIB PATH] " + lib_p + " (" + exp_p + ")");
				String res_p = resolvePath(exp_p, fInWorkspaceOk);
				
				if (getFileSystemProvider().isDir(res_p)) {
					List<String> paths = getFileSystemProvider().getFiles(res_p);
					Set<String> exts = scanner.getSrcExts();
					for (String file_p : paths) {
						int last_dot = file_p.lastIndexOf('.');
						if (last_dot != -1) {
							String ext = file_p.substring(last_dot);
							if (exts.contains(ext)) {
								addFile(file_p);
							}
						}
					}
				} else {
					fLog.error("Expanded library path \"" + exp_p + "\" does not exist");
				}
			}
			
			monitor.worked(1);
			for (String inc : scanner.getIncludePaths()) {
				String inc_path = SVDBIndexUtil.expandVars(inc, fProjectName, fInWorkspaceOk);
				fLog.debug("[INC PATH] " + inc + " (" + inc_path + ")");
				
				addIncludePath(inc_path);
			}
			
			monitor.worked(1);
			for (Entry<String, String> entry : scanner.getDefineMap().entrySet()) {
				fLog.debug("[DEFINE] " + entry.getKey() + "=" + entry.getValue());
				addDefine(entry.getKey(), entry.getValue());
			}
			
			getFileSystemProvider().closeStream(in);
			
			for (String arg_file : scanner.getArgFilePaths()) {
				arg_file = SVDBIndexUtil.expandVars(arg_file, fProjectName, fInWorkspaceOk);
				if (!cd.getArgFilePaths().contains(arg_file)) {
					processArgFile(new SubProgressMonitor(monitor, 4), arg_file); 
				}
			}
			monitor.done();
		} else {
			monitor.done();
			fLog.error("failed to open file \"" + path + "\"");
		}
	}

	@Override
	public void dispose() {
		SVDBArgFileIndexCacheData cd = (SVDBArgFileIndexCacheData)getCacheData();
		cd.getArgFileTimestamps().clear();
		for (String arg_file : cd.getArgFilePaths()) {
			long ts = getFileSystemProvider().getLastModifiedTime(arg_file);
			fLog.debug("Setting ArgFile Timestamp: " + arg_file + "=" + ts);
			cd.getArgFileTimestamps().add(ts);
		}
		
		super.dispose();
	}

	@Override
	public void fileChanged(String path) {
		fLog.debug("File changed: " + path);
		if (path.equals(getResolvedBaseLocation())) {
			// Invalidate, since this is the root file
			invalidateIndex("Argument File Changed: " + path, false);
		}
		super.fileChanged(path);
	}
}
