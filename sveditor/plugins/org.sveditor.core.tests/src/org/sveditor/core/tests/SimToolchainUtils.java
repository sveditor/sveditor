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
package org.sveditor.core.tests;

import java.util.HashMap;
import java.util.Map;

public class SimToolchainUtils {
	public static final String						QUESTA = "questa";
	public static final String						VCS    = "vcs";
	public static final String						NCSIM  = "ncsim";
	
	private static Map<String, ISimToolchain> 		fToolchainMap;
	
	static {
		fToolchainMap = new HashMap<String, ISimToolchain>();
		fToolchainMap.put(QUESTA, new QuestaSimToolChain());
	}

	public static ISimToolchain getToolchain(String id) {
		return fToolchainMap.get(id);
	}

}
