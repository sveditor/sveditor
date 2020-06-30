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
package org.eclipse.hdt.sveditor.core.tests.db;

import org.eclipse.hdt.sveditor.core.db.SVDBLocation;

import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;

public class TestSVDBLocation extends SVCoreTestCaseBase {
	
	public void testBasics() {
		SVDBLocation l = new SVDBLocation(1, 20, 30);
		assertEquals(1, l.getFileId());
		assertEquals(20, l.getLine());
		assertEquals(30, l.getPos());
	}
	
	public void testLocationNegOne() {
		SVDBLocation l = new SVDBLocation(-1);
		assertEquals(-1, l.getFileId());
		assertEquals(-1, l.getLine());
		assertEquals(-1, l.getPos());
	}

}
