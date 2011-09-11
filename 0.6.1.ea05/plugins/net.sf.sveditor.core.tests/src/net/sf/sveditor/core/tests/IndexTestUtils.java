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

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.NullProgressMonitor;

public class IndexTestUtils {
	
	public static void assertNoErrWarn(LogHandle log, ISVDBIndex index) {
		for (String file : index.getFileList(new NullProgressMonitor())) {
			List<SVDBMarker> markers = index.getMarkers(file);
			for (SVDBMarker m : markers) {
				log.debug(m.getKind() + m.getMessage());
			}
		}
		for (String file : index.getFileList(new NullProgressMonitor())) {
			List<SVDBMarker> markers = index.getMarkers(file);
			TestCase.assertEquals("File " + file, 0, markers.size());
		}
	}

	public static void assertFileHasElements(ISVDBIndexIterator index_it, String ... elems) {
		Set<String> exp = new HashSet<String>();
		for (String e : elems) {
			exp.add(e);
		}
		
		ISVDBItemIterator item_it = index_it.getItemIterator(new NullProgressMonitor());
		while (item_it.hasNext()) {
			ISVDBItemBase it = item_it.nextItem();
			String name = SVDBItem.getName(it);
			if (exp.contains(name)) {
				exp.remove(name);
			}
		}
		
		for (String e : exp) {
			TestCase.fail("Failed to find element \"" + e + "\"");
		}
	}
	
}
