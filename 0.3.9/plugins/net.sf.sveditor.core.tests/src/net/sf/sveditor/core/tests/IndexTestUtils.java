package net.sf.sveditor.core.tests;

import java.util.HashSet;
import java.util.Set;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;

import org.eclipse.core.runtime.NullProgressMonitor;

public class IndexTestUtils {
	
	public static void assertNoErrWarn(ISVDBIndexIterator index_it) {
		ISVDBItemIterator item_it = index_it.getItemIterator(new NullProgressMonitor());
		
		while (item_it.hasNext()) {
			ISVDBItemBase it = item_it.nextItem();
			if (it.getType() == SVDBItemType.Marker) {
				SVDBMarkerItem m = (SVDBMarkerItem)it;
				ISVDBChildItem ci = (ISVDBChildItem)it;
				while (ci != null && ci.getType() != SVDBItemType.File) {
					ci = ci.getParent();
				}
				
				TestCase.assertNotNull("Failed to find file of " + 
						m.getMessage(), ci);
				SVDBFile file = (SVDBFile)ci;
				
				if (m.getName().equals(SVDBMarkerItem.MARKER_ERR) ||
						m.getName().equals(SVDBMarkerItem.MARKER_WARN)) {
					System.out.println("[ERROR] ERR/WARN: " + m.getMessage() +
							" @ " + file.getName() + ":" + m.getLocation().getLine());
					TestCase.fail("Unexpected " + m.getName() + " @ " + 
							file.getName() + ":" + m.getLocation().getLine());
				}
			}
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
