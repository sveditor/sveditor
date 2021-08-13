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
package org.sveditor.core.tests.parser.db;

import org.sveditor.core.db.SVDBFile;
import org.sveditor.core.db.SVDBModuleDecl;
import org.sveditor.core.db.stmt.SVDBParamPortDecl;

import org.sveditor.core.tests.SVCoreTestCaseBase;
import org.sveditor.core.tests.SVDBTestUtils;

public class TestParseModuleDB extends SVCoreTestCaseBase {
	
	public void testPortWidth() {
		String content =
			"module top(\n" +
			"	output wire[31:0] a_misc,\n" +
			"   input retain_ctrl,\n" +
			"	input save_sel,\n" +
			"	input save_ctrl);\n" +
			"endmodule\n"
			;
			
			
		
		SVDBFile file = SVDBTestUtils.parse(content, "foo.bar");
		
		SVDBModuleDecl m = (SVDBModuleDecl)file.getChildren().iterator().next();
		
		SVDBParamPortDecl p0 = m.getPorts().get(0);
		SVDBParamPortDecl p1 = m.getPorts().get(1);

		assertEquals("wire[31:0]", p0.getTypeInfo().toString());
		assertEquals("wire", p1.getTypeInfo().toString());

	}

}
