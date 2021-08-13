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
package org.sveditor.core.tests.preproc;

import org.sveditor.core.StringInputStream;
import org.sveditor.core.Tuple;
import org.sveditor.core.preproc.SVPreProcModelFactory;
import org.sveditor.core.preproc.SVPreProcModelNode;
import org.sveditor.core.preproc.SVPreProcOutput;
import org.sveditor.core.preproc.SVPreProcessor;

import org.sveditor.core.tests.SVCoreTestCaseBase;

public class TestPreProcModelFactory extends SVCoreTestCaseBase {
	
	public void testBasics() {
		String doc = 
				"`define MY_FIELD(name) \\\n" +
				"	int name\n" +
				"\n" +
				"`define MY_CLASS(name) \\\n" +
				"	class name;\\\n" +
				"		`MY_FIELD(field_rgy);\\\n" +
				"		`MY_FIELD(field_rgy1);\\\n" +
				"		`MY_FIELD(field_rgy2);\\\n" +
				"		`MY_FIELD(field_rgy3);\\\n" +
				"\n" +
				"`MY_CLASS(foobar);\n" +
				"	int my_field;\n" +
				"endclass\n" +
				"\n"
				;
				
		SVPreProcessor pp = new SVPreProcessor(getName(), null, null, null);
		SVPreProcModelFactory f = new SVPreProcModelFactory(pp);
		
		Tuple<SVPreProcModelNode, String> result = 
				f.build(new StringInputStream(doc));
		SVPreProcModelNode root = result.first();
		System.out.println("Model:\n" + root.toString());
		
		System.out.println("Doc:\n" + result.second().toString());
		System.out.println("Annotated Model:\n" + 
				root.toString(result.second().toString()));
	}

}
