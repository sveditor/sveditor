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


package org.eclipse.hdt.sveditor.core.indent;

import java.util.ArrayList;
import java.util.List;

public class SVIndentExprToken extends SVIndentToken {
	protected List<SVIndentToken>		fExprElems;
	
	public SVIndentExprToken(String leading_ws) {
		super(SVIndentTokenType.Expression, leading_ws);
		fExprElems = new ArrayList<SVIndentToken>();
	}
	
	public List<SVIndentToken> getExprElems() {
		return fExprElems;
	}
	
	public void addExprElem(SVIndentToken elem) {
		fExprElems.add(elem);
	}

	@Override
	public String getImage() {
		StringBuilder sb = new StringBuilder();
		
		for (int i=0; i<fExprElems.size(); i++) {
			SVIndentToken tok = fExprElems.get(i);
			
			if (i > 0) {
				sb.append(tok.getLeadingWS());
			}
			sb.append(tok.getImage());
		}
		
		return sb.toString();
	}
	
	

}
