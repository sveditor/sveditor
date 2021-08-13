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
package org.sveditor.core.parser;

public class SVStringTokenListener implements ISVTokenListener {
	private StringBuilder			fString = new StringBuilder();
	private int						fCount;
	private boolean					fSpaceTokens;
	
	@Override
	public void tokenConsumed(SVToken tok) {
		if (fSpaceTokens && fCount > 0) {
			fString.append(" ");
		}
		fString.append(tok.getImage());
		fCount++;
	}

	@Override
	public void ungetToken(SVToken tok) {
		if (fCount > 0) {
			if (fCount > 1) {
				if (fSpaceTokens) {
					fString.setLength(fString.length()-tok.getImage().length()-1);
				} else {
					fString.setLength(fString.length()-tok.getImage().length());
				}
			} else {
				fString.setLength(0);
			}
			fCount--;
		}
	}
	
	public String toString() {
		return fString.toString();
	}

}
