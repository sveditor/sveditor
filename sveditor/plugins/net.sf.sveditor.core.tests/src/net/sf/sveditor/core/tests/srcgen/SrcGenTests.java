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


package net.sf.sveditor.core.tests.srcgen;

import net.sf.sveditor.core.db.index.SVDBIndexCollection;
import net.sf.sveditor.core.tests.SVDBStringDocumentIndex;
import junit.framework.Test;
import junit.framework.TestSuite;

public class SrcGenTests extends TestSuite {
	
	public static Test suite() {
		TestSuite suite = new TestSuite("SrcGenTests");
		suite.addTest(new TestSuite(TestNewClassGen.class));
		suite.addTest(new TestSuite(TestMethodGenerator.class));
		
		return suite;
	}
	
	public static SVDBIndexCollection createIndex(String doc) {
		SVDBIndexCollection index_mgr = new SVDBIndexCollection("GLOBAL");
		index_mgr.addPluginLibrary(new SVDBStringDocumentIndex(doc));
		
		return index_mgr;
	}

}
