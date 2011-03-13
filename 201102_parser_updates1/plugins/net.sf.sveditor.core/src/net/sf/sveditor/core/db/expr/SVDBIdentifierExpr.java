/****************************************************************************
 * Copyright (c) 2008-2010 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db.expr;

import java.util.ArrayList;
import java.util.List;

import net.sf.sveditor.core.db.SVDBDoNotSaveAttr;
import net.sf.sveditor.core.db.SVDBItemType;


public class SVDBIdentifierExpr extends SVDBExpr {
	private List<String>		fId;
	
	@SVDBDoNotSaveAttr
	private String				fIdStr;
	
	public SVDBIdentifierExpr() {
		this((String)null);
	}
	
	public SVDBIdentifierExpr(List<String> id) {
		super(SVDBItemType.IdentifierExpr);
		
		fId = new ArrayList<String>();
		if (id != null) {
			fId.addAll(id);
		}
	}

	public SVDBIdentifierExpr(String id) {
		super(SVDBItemType.IdentifierExpr);
		
		fId = new ArrayList<String>();
		if (id != null) {
			fId.add(id);
		}
	}

	public List<String> getId() {
		return fId;
	}
	
	public String getIdStr() {
		if (fIdStr == null) {
			StringBuilder builder = new StringBuilder();
			for (int i=0; i<fId.size(); i++) {
				builder.append(fId.get(i));
				if (i+1 < fId.size()) {
					builder.append(".");
				}
			}
			fIdStr = builder.toString();
		}
		
		return fIdStr;
	}
	
	public SVDBIdentifierExpr duplicate() {
		return new SVDBIdentifierExpr(fId);
	}
	

}
