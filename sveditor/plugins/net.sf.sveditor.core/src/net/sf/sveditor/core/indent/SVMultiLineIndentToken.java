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

public class SVMultiLineIndentToken extends SVIndentToken {
	private List<SVIndentToken>			fCommentList;
	
	public SVMultiLineIndentToken(String leading_ws) {
		super(SVIndentTokenType.MultiLineComment, leading_ws);
		fCommentList = new ArrayList<SVIndentToken>();
	}
	
	public List<SVIndentToken> getCommentLines() {
		return fCommentList;
	}
	
	public void addCommentLines(SVIndentToken tok) {
		fCommentList.add(tok);
	}

	@Override
	public String getImage() {
		StringBuilder sb = new StringBuilder();
		for (int i=0; i<fCommentList.size(); i++) {
			SVIndentToken line = fCommentList.get(i);
			
			if (i != 0) {
				sb.append(line.getLeadingWS());
			}
			sb.append(line.getImage());
			if (line.isEndLine()) {
				sb.append("\n");
			}
		}
		return sb.toString();
	}

	@Override
	public void setImage(String image) {
		System.out.println("[ERROR] cannot call SVMultiLineIndentToken.setImage()");
	}

}
