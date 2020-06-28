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
package net.sf.sveditor.core.db;

public class SVDBArgFile extends SVDBFile {
	
	public String				fBaseLocation;
	
	public SVDBArgFile() {
		this(null, null);
	}
	
	public SVDBArgFile(String path, String base) {
		super(path, SVDBItemType.ArgFile);
		fBaseLocation = (base != null)?base:"";
	}
	
	public String getBaseLocation() {
		return fBaseLocation;
	}
	
	public void setBaseLocation(String base) {
		fBaseLocation = base;
	}

}
