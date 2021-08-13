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


package org.eclipse.hdt.sveditor.core.scanner;

public class VerilogNumberParser {

	public static long parseLong(String number) throws NumberFormatException {
		int tick_index;
		String p_number = number;

		// Ignore size specification...
		if ((tick_index = number.indexOf('\'')) != -1) {
			p_number = number.substring(tick_index);
		}
		
		int radix = 10;
		
		if (p_number.startsWith("'")) {
			int radix_c = Character.toLowerCase(p_number.charAt(1));
			
			if (radix_c == 'd') {
				radix = 10;
			} else if (radix_c == 'h') {
				radix = 16;
			} else if (radix_c == 'b') {
				radix = 2;
			} else if (radix_c == 'o') {
				radix = 8;
			} else {
				System.out.println("[WARN] unknown radix \"" + 
						(char)radix_c + "\"");
			}
			p_number = p_number.substring(2);
		}
		
		// Remove any '_' separators
		if (p_number.indexOf('_') != -1) {
			p_number = p_number.replace("_", "");
		}
		
		return Long.parseLong(p_number, radix);
	}
}
