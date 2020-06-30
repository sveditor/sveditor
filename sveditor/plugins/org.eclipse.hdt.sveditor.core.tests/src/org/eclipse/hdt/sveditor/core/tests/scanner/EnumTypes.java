/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.tests.scanner;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.SVCorePlugin;
import org.eclipse.hdt.sveditor.core.StringInputStream;
import org.eclipse.hdt.sveditor.core.db.ISVDBFileFactory;
import org.eclipse.hdt.sveditor.core.db.SVDBMarker;

import junit.framework.TestCase;

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
		
		ISVDBFileFactory f = SVCorePlugin.createFileFactory();
		
		List<SVDBMarker> markers = new ArrayList<SVDBMarker>();
		/* SVDBFile file = */ f.parse(in, "enum_defs", markers);
		
	}

}
