package net.sf.sveditor.core.tests;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import net.sf.sveditor.core.db.ISVDBChildItem;
import net.sf.sveditor.core.db.ISVDBItemBase;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarker;
import net.sf.sveditor.core.db.SVDBMarker.MarkerType;
import net.sf.sveditor.core.db.index.ISVDBIndex;
import net.sf.sveditor.core.db.index.ISVDBIndexIterator;
import net.sf.sveditor.core.db.index.ISVDBItemIterator;
import net.sf.sveditor.core.log.LogHandle;

import org.eclipse.core.runtime.NullProgressMonitor;

public class IndexTestUtils {
	
	@Deprecated
	public static void assertNoErrWarn(ISVDBIndexIterator index_it) {
		ISVDBItemIterator item_it = index_it.getItemIterator(new NullProgressMonitor());
		
		while (item_it.hasNext()) {
			ISVDBItemBase it = item_it.nextItem();
			if (it.getType() == SVDBItemType.Marker) {
				SVDBMarker m = (SVDBMarker)it;
				ISVDBChildItem ci = (ISVDBChildItem)it;
				while (ci != null && ci.getType() != SVDBItemType.File) {
					ci = ci.getParent();
				}
				
				TestCase.assertNotNull("Failed to find file of " + 
						m.getMessage(), ci);
				SVDBFile file = (SVDBFile)ci;
				
				if (m.getMarkerType() == MarkerType.Error ||
						m.getMarkerType() == MarkerType.Warning) {
					System.out.println("[ERROR] ERR/WARN: " + m.getMessage() +
							" @ " + file.getName() + ":" + m.getLocation().getLine());
					TestCase.fail("Unexpected marker type " + m.getMarkerType() + " @ " + 
							file.getName() + ":" + m.getLocation().getLine());
				}
			}
		}
	}

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
