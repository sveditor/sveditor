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


package net.sf.sveditor.core.tests.search;

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
