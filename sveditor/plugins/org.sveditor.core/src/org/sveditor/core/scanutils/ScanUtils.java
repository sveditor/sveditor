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
package org.sveditor.core.scanutils;

public class ScanUtils {
	
	public static String readHierarchicalId(IBIDITextScanner scanner, int ch) {
		StringBuilder str = new StringBuilder();
		String tmp;
	
		while ((tmp = scanner.readIdentifier(ch)) != null) {
			if (scanner.getScanFwd()) {
				str.append(tmp);
			} else {
				str.insert(0, tmp);
			}
			
			ch = scanner.get_ch();
			
			if (ch == '.') {
				if (scanner.getScanFwd()) {
					str.append((char)ch);
				} else {
					str.insert(0, (char)ch);
				}
				ch = scanner.get_ch();
			} else if (ch == ':') {
				ch = scanner.get_ch();
				if (ch == ':') {
					ch = scanner.get_ch();
					if (scanner.getScanFwd()) {
						str.append("::");
					} else {
						str.insert(0, "::");
					}
				} else {
					// back out and escape
					if (ch != -1) {
						scanner.unget_ch(ch);
					}
					scanner.unget_ch(':');
					break;
				}
			} else {
				scanner.unget_ch(ch);
				break;
			}
		}
		
		if (str.length() > 0) {
			return str.toString();
		} else {
			return null;
		}
	}

}
