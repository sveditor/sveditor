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
package org.eclipse.hdt.sveditor.core.db.index;

public class SVDBIndexResourceChangeEvent {
	
	public enum Type {
		ADD,
		CHANGE,
		REMOVE
	}
	
	private String						fPath;
	private Type						fType;

	public SVDBIndexResourceChangeEvent(Type type, String path) {
		fType = type;
		fPath = path;
	}
	
	public Type getType() {
		return fType;
	}
	
	public String getPath() {
		return fPath;
	}

}