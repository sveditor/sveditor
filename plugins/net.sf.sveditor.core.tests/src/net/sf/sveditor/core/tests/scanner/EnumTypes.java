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


package net.sf.sveditor.core.tests.scanner;

import junit.framework.TestCase;
import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.StringInputStream;
import net.sf.sveditor.core.db.ISVDBFileFactory;
import net.sf.sveditor.core.db.SVDBFile;
import net.sf.sveditor.core.scanner.ScannerSVDBFileFactory;

public class EnumTypes extends TestCase {
	
	public void testEnumTypedef() {
		String enum_defs = 
			"typedef enum { A=5, B='h70, C, D } letter_t;\n" +
			"\n\n" +
			"typedef int  cmd_t;\n" +
			"\n\n" +
			"typedef enum integer {I, J, K, L} letter2_t;\n" +
			"\n\n" +
			"class foobar;\n" +
			"    typedef enum { E, F, G, H } latter_t;\n" +
			"endclass\n" +
			"\n\n";
		StringInputStream in = new StringInputStream(enum_defs);
		
		ISVDBFileFactory f = SVCorePlugin.getDefault().createFileFactory(null);
		
		SVDBFile file = f.parse(in, "enum_defs");
		
	}

}
