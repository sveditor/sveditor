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
import java.util.Map;
import java.util.Map.Entry;

import net.sf.sveditor.core.db.index.cache.ISVDBIndexCache;
import net.sf.sveditor.core.log.LogFactory;
import net.sf.sveditor.core.scanutils.ITextScanner;
import net.sf.sveditor.core.scanutils.InputStreamTextScanner;
import net.sf.sveditor.core.svf_scanner.SVFScanner;

import org.eclipse.core.runtime.IProgressMonitor;

public class SVDBArgFileIndex extends AbstractSVDBIndex {
	
	public SVDBArgFileIndex(
			String						project,
			String						root,
			ISVDBFileSystemProvider		fs_provider,
			ISVDBIndexCache				cache,
			Map<String, Object>			config) {
		super(project, root, fs_provider, cache, config);
		fLog = LogFactory.getLogHandle("SVDBArgFileIndex");
	}
	
	public String getTypeID() {
		return SVDBArgFileIndexFactory.TYPE;
	}
	
/*
	@Override
	protected void buildPreProcFileMap() {
		initPaths();
		
		// Say the index is already valid
		fPreProcFileMapValid = true;
		
		for (String file : fFilePaths) {
			String r_file = resolvePath(file);
			fLog.debug("Resolved path for \"" + file + "\" is \"" + r_file + "\"");
			SVDBFile pp_file = processPreProcFile(r_file, true);
			
			if (pp_file == null) {
				fLog.error("Failed to find file \"" + r_file + "\"");
				return;
			}
			
			SVDBFileTree ft_root = new SVDBFileTree((SVDBFile)pp_file.duplicate());
			buildPreProcFileMap(null, ft_root);
		}
	}
 */
	
	@Override
	protected SVDBBaseIndexCacheData createIndexCacheData() {
		return new SVDBArgFileIndexCacheData();
	}
	
	@Override
	protected boolean checkCacheValid() {
		long ts = getFileSystemProvider().getLastModifiedTime(getResolvedBaseLocation());
		SVDBArgFileIndexCacheData cd = (SVDBArgFileIndexCacheData)getCacheData();

		if (ts > cd.getArgFileTimestamp()) {
			fLog.debug("    ts=" + ts + " cache ArgFileTimestamp=" + cd.getArgFileTimestamp());
			return false;
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
		
		// Add an include path for the arg file location
		addIncludePath(getResolvedBaseLocationDir());
		
		InputStream in = getFileSystemProvider().openStream(getResolvedBaseLocation());
		
		if (in != null) {
			ITextScanner sc = new InputStreamTextScanner(in, getResolvedBaseLocation());
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
				String exp_f = SVDBIndexUtil.expandVars(f, true);
				fLog.debug("[FILE PATH] " + f + " (" + exp_f + ")");
				String res_f = resolvePath(exp_f);
				
				if (getFileSystemProvider().fileExists(res_f)) {
					addFile(res_f);
				} else {
					fLog.error("Expanded path \"" + exp_f + "\" does not exist");
				}
			}
			
			monitor.worked(1);
			for (String inc : scanner.getIncludePaths()) {
				String path = SVDBIndexUtil.expandVars(inc, true);
				fLog.debug("[INC PATH] " + inc + " (" + path + ")");
				
				addIncludePath(path);
			}
			
			monitor.worked(1);
			for (Entry<String, String> entry : scanner.getDefineMap().entrySet()) {
				fLog.debug("[DEFINE] " + entry.getKey() + "=" + entry.getValue());
				addDefine(entry.getKey(), entry.getValue());
			}
			
			getFileSystemProvider().closeStream(in);
			monitor.done();
		} else {
			monitor.done();
			fLog.error("failed to open file \"" + getResolvedBaseLocation() + "\"");
		}
	}

	@Override
	public void dispose() {
		SVDBArgFileIndexCacheData cd = (SVDBArgFileIndexCacheData)getCacheData();
		long ts = getFileSystemProvider().getLastModifiedTime(getResolvedBaseLocation());
		fLog.debug("Setting ArgFile Timestamp: " + ts);
		cd.setArgFileTimestamp(ts);
		super.dispose();
	}

	@Override
	public void fileChanged(String path) {
		fLog.debug("File changed: " + path);
		if (path.equals(getResolvedBaseLocation())) {
			// Invalidate, since this is the root file
			invalidateIndex();
		}
		super.fileChanged(path);
	}
	
/*	
	@Override
	protected void buildIndex(IProgressMonitor monitor) {
		getPreProcFileMap(monitor); // force pre-proc info to be built

		SubProgressMonitor sub_monitor = new SubProgressMonitor(monitor, 1);
		sub_monitor.beginTask("Processing Top-Level Files", fFilePaths.size());
		for (String file : fFilePaths) {
			file = resolvePath(file);
			SVDBFile pp_file = findPreProcFile(file);
			
			if (pp_file == null) {
				fLog.error("Failed to find file \"" + file + "\"");
				return;
			}
			
			SVDBFileTree ft_root = fFileTreeMap.get(file);
			IPreProcMacroProvider mp = createMacroProvider(ft_root);
			
			sub_monitor.subTask("Processing " + file);
			processFile(ft_root, mp);
			sub_monitor.worked(1);
		}
		
		fIndexFileMapValid = true;
		
		signalIndexRebuilt();
	}
 */	
	

}
