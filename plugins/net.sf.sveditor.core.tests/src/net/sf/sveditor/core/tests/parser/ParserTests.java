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


package net.sf.sveditor.core.tests.parser;

import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.ISVDBScopeItem;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.db.SVDBItem;
import net.sf.sveditor.core.db.SVDBItemType;
import net.sf.sveditor.core.db.SVDBMarkerItem;

public class ParserTests extends TestSuite {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("ParserTests");
		s.addTest(new TestSuite(TestParseClassBodyItems.class));
		s.addTest(new TestSuite(TestParseFunction.class));
		s.addTest(new TestSuite(TestParseModuleBodyItems.class));
		s.addTest(new TestSuite(TestParseDataTypes.class));
		s.addTest(new TestSuite(TestParseProgramBlocks.class));
		
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
	
	private static boolean findElement(ISVDBScopeItem scope, String e) {
		for (SVDBItem it : scope.getItems()) {
			if (it.getName().equals(e)) {
				return true;
			} else if (it instanceof ISVDBScopeItem) {
				if (findElement((ISVDBScopeItem)it, e)) {
					return true;
				}
			}
		}
		
		return false;
	}

}
