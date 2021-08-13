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


package org.sveditor.core.tests;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.IExtensionRegistry;
import org.eclipse.core.runtime.Platform;

public class AllReleaseTests extends TestSuite {
	
	public AllReleaseTests() {
		IExtensionRegistry e_rgy = Platform.getExtensionRegistry();
		
		IExtensionPoint ep = e_rgy.getExtensionPoint(
				"org.sveditor.core.tests", "releaseTests");
		
		for (IExtension ext : ep.getExtensions()) {
			for (IConfigurationElement el : ext.getConfigurationElements()) {
				Object suite_o = null;
				try {
					suite_o = el.createExecutableExtension("class");
				} catch (Exception e) {
					e.printStackTrace();
				}
				
				TestSuite suite = (TestSuite)suite_o;
				addTest(suite);
			}
		}
//		addTest(CoreReleaseTests.suite());
//		addTest(UiReleaseTests.suite());
	}
	
	public static Test suite() {
		return new AllReleaseTests();
	}
	
}
