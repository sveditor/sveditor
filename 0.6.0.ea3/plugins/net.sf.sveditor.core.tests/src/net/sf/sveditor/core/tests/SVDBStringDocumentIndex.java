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


package net.sf.sveditor.core.tests;

import java.io.InputStream;

import org.eclipse.core.runtime.NullProgressMonitor;

import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.index.ISVDBFileSystemChangeListener;
import net.sf.sveditor.core.db.index.ISVDBFileSystemProvider;
import net.sf.sveditor.core.db.index.SVDBLibIndex;

public class SVDBStringDocumentIndex extends SVDBLibIndex {
	
	public SVDBStringDocumentIndex(final String input) {
		super("STUB", "ROOT", new ISVDBFileSystemProvider() {
			public InputStream openStream(String path) {
				if (path.equals("ROOT")) {
					return new StringInputStream(input);
				} else {
					return null;
				}
			}
			public boolean fileExists(String path) {
				return path.equals("ROOT");
			}
			public boolean isDir(String path) {
				// Unsure
				return false;
			}
			
			public void init(String root) {}
			public long getLastModifiedTime(String path) {return 0;}
			public String resolvePath(String path) {return path;}
			public void removeFileSystemChangeListener(ISVDBFileSystemChangeListener l) {}
			public void dispose() {}
			public void closeStream(InputStream in) {}
			public void clearMarkers(String path) {}
			public void addMarker(String path, String type, int lineno, String msg) {}
			public void addFileSystemChangeListener(ISVDBFileSystemChangeListener l) {}
		}, TestIndexCacheFactory.instance(null).createIndexCache("__", "__"), null);
		init(new NullProgressMonitor());
	}
}
