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


package org.eclipse.hdt.sveditor.core.db.search;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.hdt.sveditor.core.db.ISVDBItemBase;

public class SVDBFindReferences extends SVDBElemIterator {
	
	public List<ISVDBItemBase> find_class_refs(String name) {
		List<ISVDBItemBase> ret = new ArrayList<ISVDBItemBase>();
		
		return ret;
	}

}
