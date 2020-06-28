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
package net.sf.sveditor.core.tests;

public class TestStringUtils {
	
	public static int lineOfIndex(String content, int idx) {
		int line = 1;
		
		for (int i=0; i<=idx; i++) {
			int ch = content.charAt(i);
			
			if (ch == '\n') {
				line++;
			}
		}
	
		return line;
	}

}
