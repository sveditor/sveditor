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
package org.eclipse.hdt.sveditor.core.script.launch;

import org.eclipse.hdt.sveditor.core.scanutils.ITextScanner;

public class LogMessageScannerUtils {
	
	
	public static String readPath(ITextScanner scanner, int ch) {
		StringBuilder ret = new StringBuilder();
		
		// Handle Windows-style path
		
		if ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')) {
			ret.append((char)ch);
			ch = scanner.get_ch();
			
			if (ch == ':') {
				ret.append((char)ch);
				ch = scanner.get_ch();
			}
		}
		
		while (ch == '\\' || ch == '/' || ch == '.' || ch == '-' ||
				Character.isJavaIdentifierPart(ch)) {
			ret.append((char)ch);
			ch = scanner.get_ch();
		}
		
		if (ch != -1) {
			scanner.unget_ch(ch);
		}
		
		if (ret.length() > 0) {
			return ret.toString();
		} else {
			return null;
		}
	}
	
	public static int readInt(ITextScanner scanner, int ch) {
		StringBuilder sb = new StringBuilder();
		int val = -1;
	
		while (Character.isDigit(ch)) {
			sb.append((char)ch);
			ch = scanner.get_ch();
		}
		
		scanner.unget_ch(ch);
		
		if (sb.length() > 0) {
			try {
				val = Integer.parseInt(sb.toString());
			} catch (NumberFormatException e) {}
		}
		
		return val;
	}
	
	public static String readLine(ITextScanner scanner, int ch) {
		StringBuilder sb = new StringBuilder();
		
		while (ch != -1 && ch != '\n' && ch != '\r') {
			sb.append((char)ch);
			ch = scanner.get_ch();
		}
		scanner.unget_ch(ch);
		
		if (sb.length() > 0) {
			return sb.toString();
		} else {
			return null;
		}
	}

}
