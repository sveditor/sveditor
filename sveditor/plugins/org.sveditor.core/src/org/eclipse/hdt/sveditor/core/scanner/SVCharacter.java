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


package org.sveditor.core.scanner;

public class SVCharacter {
	
	public static boolean isAlphabetic(int c) {
		return ((c >= 'a' && c <= 'z') ||
				(c >= 'A' && c <= 'Z'));
	}

	public static boolean isSVIdentifierStart(int c) {
		return (Character.isJavaIdentifierStart(c) ||
				c == '$'
				);
	}

	public static boolean isSVIdentifierPart(int c) {
		return (Character.isJavaIdentifierPart(c) ||
				c == '$'
				);
	}
	
	public static boolean isSVIdentifier(String id) {
		if (id.length() == 0) {
			return false;
		}
		
		if (!isSVIdentifierStart(id.charAt(0))) {
			return false;
		}
		
		for (int i=1; i<id.length(); i++) {
			if (!isSVIdentifierPart(id.charAt(i))) {
				return false;
			}
		}
		
		return true;
	}
	
	/**
	 * Converts a string to a SystemVerilog identifier by
	 * replacing all non-id characters with '_'
	 * 
	 * @param str
	 * @return
	 */
	public static String toSVIdentifier(String str) {
		String id;
		
		if (SVCharacter.isSVIdentifierStart(str.charAt(0))) {
			id = "" + str.charAt(0);
		} else {
			id = "_";
		}
		for (int i=1; i<str.length(); i++) {
			if (SVCharacter.isSVIdentifierPart(str.charAt(i))) {
				id += str.charAt(i);
			} else {
				id += "_";
			}
		}
		
		return id;
	}

}
