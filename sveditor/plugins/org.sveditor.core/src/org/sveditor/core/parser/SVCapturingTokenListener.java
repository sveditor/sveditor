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

import java.util.ArrayList;
import java.util.List;

public class SVCapturingTokenListener implements ISVTokenListener {
	private List<SVToken>				fTokenList;
	
	public SVCapturingTokenListener() {
		fTokenList = new ArrayList<SVToken>();
	}

	public List<SVToken> getTokenList() {
		return fTokenList;
	}

	public void tokenConsumed(SVToken tok) {
		fTokenList.add(tok.duplicate());
	}

	public void ungetToken(SVToken tok) { 
		if (fTokenList.size() > 0) {
			fTokenList.remove(fTokenList.size()-1);
		}
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		
		for (int i=0; i<fTokenList.size(); i++) {
			sb.append(fTokenList.get(i).getImage());
			if (i+1 < fTokenList.size()) {
				sb.append(" ");
			}
		}
		
		return sb.toString();
	}

}
