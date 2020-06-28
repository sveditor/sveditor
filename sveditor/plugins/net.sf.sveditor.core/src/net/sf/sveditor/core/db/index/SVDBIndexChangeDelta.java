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
package net.sf.sveditor.core.db.index;

import net.sf.sveditor.core.db.SVDBFile;

public class SVDBIndexChangeDelta {
	public enum Type {
		Add,
		Remove,
		Change
	};
	
	private Type				fType;
	private SVDBFile			fFile;
	
	public SVDBIndexChangeDelta(Type t, SVDBFile f) {
		fType = t;
		fFile = f;
	}
	
	public Type getType() { return fType; }
	
	public SVDBFile getFile() { return fFile; }

}
