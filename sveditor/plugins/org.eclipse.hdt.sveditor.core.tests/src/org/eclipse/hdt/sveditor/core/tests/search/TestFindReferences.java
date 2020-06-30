/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package org.eclipse.hdt.sveditor.core.tests.search;

import junit.framework.TestCase;

public class TestFindReferences extends TestCase {
	// Find references to class types
	// - variable declarations
	// - class extension
	// - typedef
	
	
	public void testFindExtensionRef() {
		String content =
			"class base;\n" +
			"endclass\n" +
			"\n" +
			"class extension extends base;\n" +
			"endclass\n"
			;
		
		
						
	}

}
