/****************************************************************************
 * Copyright (c) 2008-2011 Matthew Ballance and others.
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


package net.sf.sveditor.core.db;


public class SVDBModportTFPortsDecl extends SVDBModportPortsDecl {
	public enum ImpExpType {
		Import,
		Export
	};
	
	public ImpExpType				fImpExpType;
	
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
