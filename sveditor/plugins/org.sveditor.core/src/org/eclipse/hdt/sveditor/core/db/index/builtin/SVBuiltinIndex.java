/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.sveditor.core.db.index.builtin;

import java.io.InputStream;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.sveditor.core.Tuple;
import org.sveditor.core.builder.ISVBuilderOutput;
import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBFileTree;
import org.sveditor.core.db.SVDBMarker;
import org.sveditor.core.db.index.ISVDBFileSystemProvider;
import org.sveditor.core.db.index.ISVDBIndex;
import org.sveditor.core.db.index.ISVDBIndexChangeListener;
import org.sveditor.core.db.index.ISVDBIndexOperation;
import org.sveditor.core.db.index.SVDBDeclCacheItem;
import org.sveditor.core.db.index.SVDBFilePath;
import org.sveditor.core.db.index.SVDBIncFileInfo;
import org.sveditor.core.db.index.SVDBIndexConfig;
import org.sveditor.core.db.index.SVDBIndexResourceChangeEvent;
import org.sveditor.core.db.index.builder.ISVDBIndexBuilder;
import org.sveditor.core.db.index.builder.ISVDBIndexChangePlan;
import org.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.sveditor.core.db.refs.ISVDBRefSearchSpec;
import org.sveditor.core.db.refs.ISVDBRefVisitor;
import org.sveditor.core.db.search.ISVDBFindNameMatcher;
import org.sveditor.core.preproc.ISVStringPreProcessor;

public class SVBuiltinIndex implements ISVDBIndex {

	@Override
	public List<SVDBDeclCacheItem> findGlobalScopeDecl(
			IProgressMonitor 		monitor, 
			String 					name,
			ISVDBFindNameMatcher 	matcher) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<String> getFileList(IProgressMonitor monitor, int flags) {
		return null;
	}

	@Override
	public SVDBFile findFile(IProgressMonitor monitor, String filename) {
		return null;
	}

	@Override
	public SVDBFile findPreProcFile(IProgressMonitor monitor, String filename) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<SVDBDeclCacheItem> findPackageDecl(IProgressMonitor monitor, SVDBDeclCacheItem pkg_item) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFile getDeclFile(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFile getDeclFilePP(IProgressMonitor monitor, SVDBDeclCacheItem item) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<SVDBIncFileInfo> findIncludeFiles(String root, int flags) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void execOp(IProgressMonitor monitor, ISVDBIndexOperation op, boolean sync) {
		// TODO Auto-generated method stub

	}

	@Override
	public List<SVDBFilePath> getFilePath(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void findReferences(IProgressMonitor monitor, ISVDBRefSearchSpec ref_spec, ISVDBRefVisitor ref_matcher) {
		// TODO Auto-generated method stub

	}

	@Override
	public ISVDBIndexChangePlan createIndexChangePlan(List<SVDBIndexResourceChangeEvent> changes) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void execIndexChangePlan(IProgressMonitor monitor, ISVDBIndexChangePlan plan) {
		// TODO Auto-generated method stub

	}

	@Override
	public Tuple<SVDBFile, SVDBFile> parse(IProgressMonitor monitor, InputStream in, String path,
			List<SVDBMarker> markers) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ISVStringPreProcessor createPreProc(String path, InputStream in, int limit_lineno) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ISVDBFileSystemProvider getFileSystemProvider() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setFileSystemProvider(ISVDBFileSystemProvider fs_provider) {
		// TODO Auto-generated method stub

	}

	@Override
	public void setBuilderOutput(ISVBuilderOutput out) {
		// TODO Auto-generated method stub

	}

	@Override
	public void init(IProgressMonitor monitor, ISVDBIndexBuilder builder) {
		// TODO Auto-generated method stub

	}

	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

	@Override
	public String getBaseLocation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getProject() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setGlobalDefine(String key, String val) {
		// TODO Auto-generated method stub

	}

	@Override
	public void clearGlobalDefines() {
		// TODO Auto-generated method stub

	}

	@Override
	public String getTypeID() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<String> getFileList(IProgressMonitor monitor) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<SVDBMarker> getMarkers(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFile findFile(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFileTree findFileTree(String path, boolean is_argfile) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public SVDBFile findPreProcFile(String path) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean doesIndexManagePath(String path) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void rebuildIndex(IProgressMonitor monitor) {
		// TODO Auto-generated method stub

	}

	@Override
	public void addChangeListener(ISVDBIndexChangeListener l) { }

	@Override
	public void removeChangeListener(ISVDBIndexChangeListener l) { }

	@Override
	public ISVDBIndexCache getCache() {
		return null;
	}

	@Override
	public void loadIndex(IProgressMonitor monitor) {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean isLoaded() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isFileListLoaded() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public SVDBIndexConfig getConfig() {
		// TODO Auto-generated method stub
		return null;
	}

}
