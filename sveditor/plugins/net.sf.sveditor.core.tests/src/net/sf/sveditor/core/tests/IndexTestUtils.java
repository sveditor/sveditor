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


package net.sf.sveditor.core.tests;

import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import net.sf.sveditor.core.Tuple;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBDeclCache;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexInt;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBIndexOperation;
import net.sf.sveditor.core.db.index.ISVDBIndexOperationRunner;
import net.sf.sveditor.core.db.index.SVDBDeclCacheItem;
import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.db.search.SVDBFindDefaultNameMatcher;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;

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
					for (SVDBMarker m : markers) {
						int fileid = -1, lineno = -1;
						String filename = null;
						
						if (m.getLocation() != null) {
							fileid = m.getLocation().getFileId();
							lineno = m.getLocation().getLine();
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
					List<SVDBDeclCacheItem> result = index_it.findGlobalScopeDecl(
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
					
					TestCase.assertEquals("Index contains " + e, 0, result.size());
				}
			}
		};
		
		index_it.execOp(new NullProgressMonitor(), op, true);
	}

	public static ISVDBIndexIterator buildIndex(String doc, String filename) {
		SVDBFile file = SVDBTestUtils.parse(doc, filename);
		ISVDBIndexIterator target_index = new FileIndexIterator(file);
		
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
	
}
