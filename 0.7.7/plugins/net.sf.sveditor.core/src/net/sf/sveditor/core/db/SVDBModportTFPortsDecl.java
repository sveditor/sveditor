/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Matthew Ballance - initial implementation
 ****************************************************************************/


package net.sf.sveditor.core.db;


public class SVDBModportTFPortsDecl extends SVDBModportPortsDecl {
	public enum ImpExpType {
		Import,
		Export
	};
	
	ImpExpType				fImpExpType;
	
	public SVDBModportTFPortsDecl() {
		super(SVDBItemType.ModportTFPortsDecl);
	}
	
	public void setImpExpType(String type) {
		if (type.equals("import")) {
			setImpExpType(ImpExpType.Import);
		} else {
			setImpExpType(ImpExpType.Export);
		}
	}
	
	public void setImpExpType(ImpExpType type) {
		fImpExpType = type;
	}
	
	public ImpExpType getImpExpType() {
		return fImpExpType;
	}

}
