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


package net.sf.sveditor.core.tests.parser;

import net.sf.sveditor.core.SVCorePlugin;
import net.sf.sveditor.core.parser.SVParseException; 
import junit.framework.TestCase;

public class TestParseAssertions extends TestCase {
	
	public void testOvmXbusAssertions() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTest("testOvmXbusAssertions",
				"/data/assertions/xbus_assertions.sv",
				new String[] {"xbus_if"});
	}

	public void testOvmXbusAssertions_repetition() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTest("testOvmXbusAssertions",
				"/data/assertions/xbus_assertions.sv",
				new String[] {"xbus_if"});
	}

	public void testBasicProperties() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTest("testOvmXbusAssertions",
				"/data/assertions/basic_properties.sv",
				new String[] {"my_module"});
	}

	public void testSavedValueProperty() throws SVParseException {
		SVCorePlugin.getDefault().enableDebug(false);
		ParserTests.runTest("testSavedValueProperty",
				"/data/assertions/saved_value_property.sv",
				new String[] {"saved_value_property","p1"});
	}

}
