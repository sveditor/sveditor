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

public class SVDBModportTFPort extends SVDBChildItem {
	public String			fId;
	public SVDBTask		fTFPrototype;
	
	public SVDBModportTFPort() {
		super(SVDBItemType.ModportTFPort);
	}
	
	public void setId(String id) {
		fId = id;
	}
	
	public String getId() {
		return fId;
	}
	
	public void setPrototype(SVDBTask p) {
		fTFPrototype = p;
	}
	
	public SVDBTask getPrototype() {
		return fTFPrototype;
	}
	
	@Override
	public void accept(ISVDBVisitor v) {
		v.visit_modport_tf_port(this);
	}

}
