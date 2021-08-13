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
package org.eclipse.hdt.sveditor.ui.argfile.editor;

import org.eclipse.jface.text.rules.IWordDetector;

public class SVArgFileWordDetector implements IWordDetector {
	private boolean				fStartsWithPlus;
	private char				fLastCh = ' ';

	public boolean isWordStart(char c) {
		fStartsWithPlus = (c == '+');
		fLastCh = ' ';
		return (Character.isJavaIdentifierStart(c) || c == '+' || c == '-');
	}

	public boolean isWordPart(char c) {
		if (fLastCh == '+' && fStartsWithPlus) {
			return false;
		} else {
			fLastCh = c;
			return (Character.isJavaIdentifierPart(c) || c == '+');
		}
	}

}
