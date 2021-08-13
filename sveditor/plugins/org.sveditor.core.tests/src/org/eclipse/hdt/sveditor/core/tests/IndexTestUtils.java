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


package org.eclipse.hdt.sveditor.core.tests;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.hdt.sveditor.core.Tuple;
import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;
import org.eclipse.hdt.sveditor.core.db.ISVDBNamedItem;
import org.eclipse.hdt.sveditor.core.db.SVDBFile;
import org.eclipse.hdt.sveditor.core.db.SVDBLocation;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker.MarkerType;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBDeclCache;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndex;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexInt;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexIterator;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexOperation;
import org.eclipse.hdt.sveditor.core.db.index.ISVDBIndexOperationRunner;
import org.eclipse.hdt.sveditor.core.db.index.SVDBDeclCacheItem;
import org.eclipse.hdt.sveditor.core.db.index.SVDBIndexCollection;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCache;
import org.eclipse.hdt.sveditor.core.db.index.cache.ISVDBIndexCacheMgr;
import org.eclipse.hdt.sveditor.core.db.search.ISVDBFindNameMatcher;
import org.eclipse.hdt.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import org.eclipse.hdt.sveditor.core.log.LogHandle;

public class IndexTestUtils {
	
	public static void assertNoErrWarn(final LogHandle log, ISVDBIndex index) {

		
		ISVDBIndexOperation check_op = new ISVDBIndexOperation() {
			public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
				for (String file : index.getFileList(new NullProgressMonitor())) {
					List<SVDBMarker> markers = index.getMarkers(file);
					for (SVDBMarker m : markers) {
						log.debug("[MARKER]" + m.getKind() + m.getMessage());
					}
				}				

				for (String file : index.getFileList(new NullProgressMonitor())) {
					List<SVDBMarker> markers = index.getMarkers(file);
//					for (SVDBMarker m : markers) {
					for (int i=0; i<markers.size(); i++) {
						SVDBMarker m = markers.get(i);
						
						if (m.getMarkerType() == MarkerType.Task) {
							markers.remove(i);
							i--;
							continue;
						}

						int fileid = -1, lineno = -1;
						String filename = null;
						
						if (m.getLocation() != -1) {
							fileid = SVDBLocation.unpackFileId(m.getLocation());
							lineno = SVDBLocation.unpackLineno(m.getLocation());
						}
						
						if (index instanceof ISVDBIndexInt) {
							filename = ((ISVDBIndexInt)index).getFileFromId(fileid);
						}
						
						log.debug("Marker: " + m.getMessage() + " @ " + 
								filename + ":" + lineno);
					}
					TestCase.assertEquals("File " + file, 0, markers.size());
				}
			}
		};
		
		index.execOp(new NullProgressMonitor(), check_op, true);

	}

	public static void assertNoErrWarn(LogHandle log, SVDBIndexCollection index_mgr) {
		for (ISVDBIndex index : index_mgr.getIndexList()) {
			for (String file : index.getFileList(new NullProgressMonitor())) {
				List<SVDBMarker> markers = index.getMarkers(file);
				for (SVDBMarker m : markers) {
					log.debug("[MARKER]" + m.getKind() + m.getMessage());
				}
			}
			for (String file : index.getFileList(new NullProgressMonitor())) {
				List<SVDBMarker> markers = index.getMarkers(file);
				for (int i=0; i<markers.size(); i++) {
					SVDBMarker m = markers.get(i);
					if (m.getMarkerType() == MarkerType.Task) {
						markers.remove(i);
						i--;
						continue;
					}
				}
				TestCase.assertEquals("File " + file, 0, markers.size());
			}
		}
	}
	
	public static void assertFileHasElements(ISVDBIndexIterator index_it, String ... elems) {
		assertFileHasElements(null, index_it, elems);
	}

	public static void assertFileHasElements(
			final LogHandle 			log, 
			final ISVDBIndexIterator 	index_it, 
			final String 		... 	elems) {
		final List<String> exp = new ArrayList<String>();
		for (String e : elems) {
			exp.add(e);
		}
		
		ISVDBIndexOperation op = new ISVDBIndexOperation() {
			
			public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
				int i=0;
				while (i < exp.size()) {
					List<SVDBDeclCacheItem> result = index.findGlobalScopeDecl(
							new NullProgressMonitor(), 
							exp.get(i), SVDBFindDefaultNameMatcher.getDefault());
					
					if (result.size() > 0) {
						exp.remove(i);
					} else {
						i++;
					}
				}
			}
		};
		
		index_it.execOp(new NullProgressMonitor(), op, true);
		
		StringBuilder failed_message = new StringBuilder("Failed to find elements: ");
		for (String e : exp) {
			failed_message.append(e + " ");
		}
	
		TestCase.assertEquals(failed_message.toString(), 0, exp.size());
	}

	public static void assertDoesNotContain(
			final ISVDBIndexIterator index_it, 
			String ... elems) {
		final Set<String> exp = new HashSet<String>();
		for (String e : elems) {
			exp.add(e);
		}
		
		ISVDBIndexOperation op = new ISVDBIndexOperation() {
			public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
				for (String e : exp) {
					List<SVDBDeclCacheItem> result = index_it.findGlobalScopeDecl(
							new NullProgressMonitor(), 
							e, SVDBFindDefaultNameMatcher.getDefault());
					
					if (result.size() > 0) {
						System.out.println("Find Item: " + result.get(0).getSVDBItem());
					}
					
					TestCase.assertEquals("Index contains " + e, 0, result.size());
				}
			}
		};
		
		index_it.execOp(new NullProgressMonitor(), op, true);
	}

	public static ISVDBIndexIterator buildIndex(String doc, String filename, ISVDBIndexCacheMgr cache_mgr) {
		SVDBFile file = SVDBTestUtils.parse(doc, filename);
		ISVDBIndexCache cache = FileIndexIterator.createCache(cache_mgr);
		ISVDBIndexIterator target_index = new FileIndexIterator(file, cache);
		
		return target_index;
	}
	
	public static ISVDBItemBase find(ISVDBDeclCache searcher, String name) {
		List<SVDBDeclCacheItem> result = searcher.findGlobalScopeDecl(
				new NullProgressMonitor(), name, 
				SVDBFindDefaultNameMatcher.getDefault());
		
		if (result.size() > 0) {
			return result.get(0).getSVDBItem();
		} else {
			return null;
		}
	}
	
	public static Tuple<SVDBFile, SVDBFile> parse(
			ISVDBIndexOperationRunner 	runner, 
			final InputStream			in,
			final String				path,
			final List<SVDBMarker>		markers) {
		final Tuple<SVDBFile, SVDBFile> result = new Tuple<SVDBFile, SVDBFile>(null, null);

		ISVDBIndexOperation op = new ISVDBIndexOperation() {
			
			public void index_operation(IProgressMonitor monitor, ISVDBIndex index) {
				Tuple<SVDBFile, SVDBFile> file = index.parse(
						new NullProgressMonitor(), 
						in, 
						path, 
						markers);
				if (file != null) {
					result.setFirst(file.first());
					result.setSecond(file.second());
				}
			}
		};
		
		runner.execOp(new NullProgressMonitor(), op, true);
		
		return result;
	}
	
	public static Tuple<SVDBFile, SVDBFile> parse(
			ISVDBIndex				index,
			String					path,
			List<SVDBMarker>		markers) {
		InputStream in = index.getFileSystemProvider().openStream(path);
		return parse(index, in, path, markers);
	}
	
}
