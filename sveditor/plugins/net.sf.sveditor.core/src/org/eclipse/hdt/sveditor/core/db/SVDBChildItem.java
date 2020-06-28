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


package org.eclipse.hdt.sveditor.core.db;

import org.eclipse.hdt.sveditor.core.db.attr.SVDBParentAttr;

public class SVDBChildItem extends SVDBItemBase implements ISVDBChildItem {
	@SVDBParentAttr
	public ISVDBChildItem 			fParent;
	
	public SVDBChildItem(SVDBItemType type) {
		super(type);
	}

	public ISVDBChildItem getParent() {
		return fParent;
	}

	public void setParent(ISVDBChildItem parent) {
		fParent = parent;
	}

	/*
	public Iterable getChildren() {
		return EmptySVDBChildItemIterable.iterable;
	}
	 */
	
}
