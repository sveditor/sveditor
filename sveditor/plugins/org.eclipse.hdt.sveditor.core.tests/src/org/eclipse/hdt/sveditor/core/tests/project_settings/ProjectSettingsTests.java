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
package org.eclipse.hdt.sveditor.core.tests.project_settings;

import junit.framework.TestSuite;
import org.eclipse.hdt.sveditor.core.tests.SVCoreTestCaseBase;

public class ProjectSettingsTests extends SVCoreTestCaseBase {
	
	public static TestSuite suite() {
		TestSuite s = new TestSuite("ProjectSettingsTests");
		s.addTest(new TestSuite(TestProjectSettingsVarRefs.class));
		s.addTest(new TestSuite(TestProjectSettingChanges.class));
		return s;
	}
	
}
