/****************************************************************************
 * Copyright (c) 2008-2014 Matthew Ballance and others.
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


package org.sveditor.ui.explorer;

import org.eclipse.core.runtime.IAdaptable;
import org.sveditor.core.db.SVDBFile;

public class ProjectPathsFileWrapper implements IAdaptable {
	private SVDBFile				fFile;
	
	public ProjectPathsFileWrapper(SVDBFile f) {
		fFile = f;
	}
	
	public SVDBFile getFile() {
		return fFile;
	}

	@SuppressWarnings("rawtypes")
	public Object getAdapter(Class adapter) {
		if (adapter.equals(SVDBFile.class)) {
			return fFile;
		}
		return null;
	}
	
}
