package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;
import net.sf.sveditor.core.db.SVDBScopeItem;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class ParserTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("ParserTests");
		s.addTest(new TestSuite(TestParseClassBodyItems.class));
		s.addTest(new TestSuite(TestParseFunction.class));
		s.addTest(new TestSuite(TestParseModuleBodyItems.class));
		
		return s;
	}
	
	public static SVDBFile parse(String content, String filename) {
		SVDBFile file = null;
		ISVDBFileFactory factory = SVCorePlugin.getDefault().createFileFactory(null);
		
		file = factory.parse(new StringInputStream(content), filename);
		
		return file;
	}
	
	public static void assertNoErrWarn(SVDBFile file) {
		for (SVDBItem it : file.getItems()) {
			if (it.getType() == SVDBItemType.Marker) {
				SVDBMarkerItem m = (SVDBMarkerItem)it;
				
				if (m.getName().equals(SVDBMarkerItem.MARKER_ERR) ||
						m.getName().equals(SVDBMarkerItem.MARKER_WARN)) {
					TestCase.fail("Unexpected " + m.getName() + " @ " + 
							file.getName() + ":" + m.getLocation().getLine());
				}
			}
		}
	}
	
	public static void assertFileHasElements(SVDBFile file, String ... elems) {
		for (String e : elems) {
			if (!findElement(file, e)) {
				TestCase.fail("Failed to find element \"" + e + "\" in file " + file.getName());
			}
		}
	}
	
	private static boolean findElement(SVDBScopeItem scope, String e) {
		for (SVDBItem it : scope.getItems()) {
			if (it.getName().equals(e)) {
				return true;
			} else if (it instanceof SVDBScopeItem) {
				if (findElement((SVDBScopeItem)it, e)) {
					return true;
				}
			}
		}
		
		return false;
	}

}
