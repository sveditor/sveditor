/* 
 * Copyright (c) 2008-2020 Matthew Ballance and others.
 *
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * https://www.eclipse.org/legal/epl-2.0/.
 *
 * SPDX-License-Identifier: EPL-2.0
 *
 */
package org.eclipse.hdt.sveditor.ui.tests.console;

import junit.framework.TestSuite;

public class ConsoleTests extends TestSuite {
	
	public ConsoleTests() {
		addTest(new TestSuite(TestPathPatternMatcher.class));
	}

	public static TestSuite suite() {
		return new ConsoleTests();
	}
}
