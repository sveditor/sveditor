/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.indent;

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
